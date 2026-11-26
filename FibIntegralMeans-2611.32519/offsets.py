import sys
def fm(m):
    a,b=0,1
    for bit in bin(m)[2:]:
        c=a*(2*b-a)%m; d=(a*a+b*b)%m
        a,b=(d,(c+d)%m) if bit=='1' else (c,d)
    return a
M=int(sys.argv[1]); res={}
for m in range(5,M,2):
    f=fm(m)
    for c in range(-12,13):
        if (f+c)%m==0:
            res.setdefault(c,[]).append(m)
for c in range(-12,13):
    L=res.get(c,[]); print('%+3d'%c,len(L),L[:8])
