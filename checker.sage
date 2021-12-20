import sys
from sage.numerical.mip import MIPSolverException
from time import time


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

#checking if \mathcal{L}(P,\tau) has a solution for the given comb = \tau 
def check_case(a,d,comb): #coordinates and dimensions of the box P, comb

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
    
    return check_cover(ss,P_rep,comb,"PPL")

#end of good/bad function


#main part

n = int(sys.argv[1])

fo_name = './output/'+str(n)+'.csv'

with open(fo_name) as fi:
    cases_done_str = fi.readlines()

def empty_rep(a): #replacing empty string with -1
    if a=='':
        return -1
    return a
    
subcases = []
for line in cases_done_str:
    subcases.append([Rational(empty_rep(x)) for x in line.rstrip().split(',')])
    
tm = time()

subdivisions = 0
for sc in subcases:
    if sc[12]==-1:
        subdivisions += 1
    else:
        res = check_case(sc[0:6],sc[6:12],sc[12:18])
        if not(res):
            print("failed check",sc)

tm = time()-tm

print("input cases:",len(subcases)-2*subdivisions)

if len(subcases)>0:
    print(len(subcases),"subcases considered",tm/3600,"hours total",tm/len(subcases),"seconds per subcase")
else:
    print("no cases to consider")
