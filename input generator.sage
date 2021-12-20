#generates files 10000.txt ... 10511.txt in the input folder with boxes in each region
M = 10 
M2 = M/2
h = 1/(2*M) #initial box size
fc = ['' for i in range(512)]
for k1 in range(0,M):
    for k2 in range(0,M):
        for k3 in range(0,M):
            for k4 in range(0,2*M):
                for k5 in range(0,2*M):
                    for k6 in range(0,2*M):
                        if k2+k4<=k1+k6+1 and k1+k6<=k3+k5+1:
                            fc[floor(k1/M2)*256+floor(k2/M2)*128+floor(k3/M2)*64+floor(k4/M2)*16+floor(k5/M2)*4+floor(k6/M2)] += (",".join(str(x) for x in [k1*h,k2*h,k3*h,k4*h,k5*h,k6*h,h,h,h,h,h,h]) + "\r\n")

for i in range(512):
    f = open('./input/'+str(10000+i)+'.csv','a')
    f.write(fc[i])
    f.close()        
