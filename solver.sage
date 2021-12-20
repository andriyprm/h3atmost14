import sys
from sage.numerical.mip import MIPSolverException
from time import time

def log(a,b,c,d):
    res = ",".join([str(x) for x in a])
    res += "," + ",".join([str(x) for x in b])
    res += "," + ",".join([str(x) for x in c]) + "," + str(d)+ "\r\n"
    fo.write(res)

#vertices of the cube
vers = [[0,0,0],[0,0,1],[0,1,0],[1,0,0],[0,1,1],[1,0,1],[1,1,0],[1,1,1]] 

#edges - vertex and direction vector
edges = [[[0,0,0],[1,0,0]], #0
         [[1,0,0],[0,1,0]], #1
         [[0,1,0],[1,0,0]], #2
         [[0,0,0],[0,1,0]], #3
         [[0,0,1],[1,0,0]], #4
         [[1,0,1],[0,1,0]], #5
         [[0,1,1],[1,0,0]], #6
         [[0,0,1],[0,1,0]], #7
         [[0,0,0],[0,0,1]], #8
         [[1,0,0],[0,0,1]], #9
         [[1,1,0],[0,0,1]], #10
         [[0,1,0],[0,0,1]]] #11

#v_edges - indexes of vertices defining the edge
v_edges = [[0, 3],
           [3, 6],
           [2, 6],
           [0, 2],
           [1, 5],
           [5, 7],
           [4, 7],
           [1, 4],
           [0, 1],
           [3, 5],
           [6, 7],
           [2, 4]]
        
#indexes of edges adjacent to each vertex, in the order of directions
adj_edges = [[0,3,8],[4,7,8],[2,3,11],[0,1,9],[6,7,11],[4,5,9],[2,1,10],[6,5,10]] 

#############
#possible choices for the mapping \tau

#for each face we choose an edje contained in it
#faces are ordered as follows: x=0, x=1, y=0, y=1, z=0, z=1
res = []
for i1 in range(4):
    for i2 in range(4):
        for j1 in range(4):
            for j2 in range(4):
                for k1 in range(4):
                    for k2 in range(4):
                        res.append([[3,8,7,11][i1],[1,9,5,10][i2],[0,8,4,9][j1],[2,11,6,10][j2],[0,1,2,3][k1],[4,5,6,7][k2]])

combs = [] #we want \tau to be injective
for r in res:
    if len(set(r))==6:
        combs.append(r)

order = Permutations(range(len(combs))).random_element() #the order of tries, starting with random

#the following choices are used when the box is still rather big
combs16 =[[8, 1, 0, 2, 3, 6] ,
[3, 1, 9, 10, 2, 6] ,
[3, 1, 8, 10, 2, 4] ,
[8, 1, 0, 2, 3, 7] ,
[3, 1, 8, 10, 0, 4] ,
[3, 10, 4, 6, 2, 7] ,
[8, 9, 0, 11, 1, 4] ,
[7, 1, 8, 11, 3, 6] ,
[3, 1, 9, 10, 0, 5] ,
[3, 10, 8, 2, 0, 5] ,
[3, 10, 9, 11, 1, 6] ,
[3, 1, 9, 2, 0, 7] ,
[8, 5, 9, 10, 3, 7] ,
[8, 5, 4, 2, 1, 6] ,
[3, 10, 4, 2, 0, 5] ,
[8, 9, 0, 2, 3, 4]]

#############

def check_cover(ss,P_rep,comb,solver_name): 
    #ss contains 6 lists of 4 elements each describing the vertices of R_P\cap F_{ij} i.e. the rectangles on the faces
    #P_rep is a list of half-spaces representing Q_P given as lists of coefficients of the linear inequalities
    #comb is a list of 6 edge indexes representing \mathcal{E}
    #solver_name either "CVXOPT" for numerical of "PPL" for exact
    p = MixedIntegerLinearProgram(solver = solver_name)
    w = p.new_variable()

    #point inside
    def add_tr(x,k):#x is a point which is required to be inside the translate Q_P+(w[k],w[k+1],w[k+2])
        for rp in P_rep:
            p.add_constraint(rp[0]+sum((x[i]+w[k+i])*rp[i+1] for i in range(3))>=0)

    #point on an edge, given by a parameter w[kk]
    def add_seg(ei,k,kk): #ei - edge index, [v,u]=edges[ei], require that v+w[kk]u is inside the translate Q_P+(w[k],w[k+1],w[k+2])
        for rp in P_rep:
            p.add_constraint(rp[0]+sum((edges[ei][0][i]+w[kk]*edges[ei][1][i]+w[k+i])*rp[i+1] for i in range(3))>=0)

    #a_v=(w[3*v],w[3*v+1],w[3*v+2]) is the translate covering v-th vertex, v=0..7; variables w[0]..w[23] used
    for v in range(8):
        add_tr(vers[v],3*v)

    #(w[24+3*f],w[25+3*f],w[26+3*f])=b_f is the translate covering the corresponding rectangle on f-th face, f=0..5
    #we require R_P\cap F_{ij}\subset b_{ij}+Q_P
    #w[24]..w[41] are used
    for f in range(6):
        for t in range(4):
            add_tr(ss[f][t],24+3*f)
        
    l=42 #index for new variables that will be added
    #w[42]..w[59] are used
    for i in range(12):
        if i not in comb:
            #if an edge is not in \mathcal{E} we require the point with parameter w[l] on that edge to belong to both translates
            #that cover the endpoints of this edge
            add_seg(i,3*v_edges[i][0],l) 
            add_seg(i,3*v_edges[i][1],l) 
            l += 1
        else:
            #otherwise w[l] w[l+1] are parameters defining the middle portion of the edge
            #w[l] covered by the translate for the beginning of the edge
            add_seg(i,3*v_edges[i][0],l)
            #w[l+1] covered by the translate for the end of the edge
            add_seg(i,3*v_edges[i][1],l+1)
            #both points covered by the translate covering the rectangle on the f-the face for which this edge is comb[f]
            f = 0
            while comb[f]!=i:
                f += 1
            add_seg(i,24+3*f,l) 
            add_seg(i,24+3*f,l+1)
            l += 2

    p.set_objective(None)
    try:
        p.solve()
        return True
    except MIPSolverException:
        return False


#########

#checking if \mathcal{L}(P,\tau) has a solution for at least one \tau from combs
#returns the comb, or [] if not found
def check_case(a,d,dep): #coordinates and dimensions of the box P, recursion depth

    global order
    
    ss = [[[0,a[0],a[1]],[0,a[0]+d[0],a[1]],[0,a[0],a[1]+d[1]],[0,a[0]+d[0],a[1]+d[1]]],
          [[1,a[0],a[1]],[1,a[0]+d[0],a[1]],[1,a[0],a[1]+d[1]],[1,a[0]+d[0],a[1]+d[1]]],
          [[a[2],0,a[3]],[a[2]+d[2],0,a[3]],[a[2],0,a[3]+d[3]],[a[2]+d[2],0,a[3]+d[3]]],
          [[a[2],1,a[3]],[a[2]+d[2],1,a[3]],[a[2],1,a[3]+d[3]],[a[2]+d[2],1,a[3]+d[3]]],
          [[a[4],a[5],0],[a[4]+d[4],a[5],0],[a[4],a[5]+d[5],0],[a[4]+d[4],a[5]+d[5],0]],
          [[a[4],a[5],1],[a[4]+d[4],a[5],1],[a[4],a[5]+d[5],1],[a[4]+d[4],a[5]+d[5],1]]] #vertices of R_P\cap F_{ij} 

    QP = Polyhedron(ieqs=[(0,1,0,0)]) #anything containing the cube

    #intersecting 64 polyhedra O_p where p is a vertex of P
    for i0 in range(4):
        for i2 in range(4):
            for i4 in range(4):
                Op = Polyhedron(vertices=[ss[0][i0],ss[1][i0],ss[2][i2],ss[3][i2],ss[4][i4],ss[5][i4]])
                QP = QP.intersection(Op)
    if QP.dim()<3:
        return False
    
    #half-spaces representing Q_P given as lists of coefficients of the linear inequalities
    P_rep = [[hrep[j] for j in range(4)] for hrep in QP.Hrepresentation()]

    if dep<=6: #using combs16 when shallow
        for comb in combs16:
            #if a solution is found numerically, also check exact one
            if check_cover(ss,P_rep,comb,"CVXOPT") and check_cover(ss,P_rep,comb,"PPL"):
                return comb
        return [] #none worked
            
    #searching through all combs
    for c_ind in range(len(combs)):        
        comb = combs[order[c_ind]]
        #if a solution is found numerically, also check exact one
        if check_cover(ss,P_rep,comb,"CVXOPT") and check_cover(ss,P_rep,comb,"PPL"):
            #successful comb is moved to the beginning of the order list
            order = [order[c_ind]] + order[:c_ind]+order[(c_ind+1):]
            return comb

    #no comb from the list works
    return []

#end of good/bad function

#main recursive function, return number of subcases
def rec_check(a,d,dep=0):
    cc = check_case(a,d,dep)
    if cc != []:
        log(a,d,cc,dep)
        return 1
    else:
        log(a,d,['','','','','',''],dep)
        arg = -1 
        maxd = -1
        for i in range(6):
            if d[i]>maxd:
                maxd = d[i]
                arg = i
        aa = a.copy()
        dd = d.copy()
        dd[arg] /= 2
        res = rec_check(aa,dd,dep+1)
        aa[arg] += maxd/2
        res += rec_check(aa,dd,dep+1)
        return res

#end of main rec function

#main part

n = int(sys.argv[1])

fo = open('./output/'+str(n)+'.csv','w')

with open('./input/'+str(n)+'.csv') as fi:
    cases_str = fi.readlines()

cases = []
for line in cases_str:
    cases.append([Rational(x) for x in line.rstrip().split(',')])

tm = time()

for a in cases:    
    rec_check(a[0:6],[a[6]]*6)    

fo.close()

tm = time()-tm

if len(cases)>0:
    print(len(cases),"cases considered",tm/3600,"hours total",tm/len(cases),"seconds per case")
else:
    print("no cases to consider")
