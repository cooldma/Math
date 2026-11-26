/* naive.c: independent brute force, prints odd m in [5,hi) with m | F_m + t (t = tA if 3!|m else tB) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static u64 fibmod(u64 n, u64 M){ /* simple matrix power, independent of fibsearch */
  u64 a=1,b=0,c=0,d=1, x=1,y=1,z=1,w=0; /* result = I, base = Q */
  while(n){ if(n&1){ u64 na=((u128)a*x+(u128)b*z)%M, nb=((u128)a*y+(u128)b*w)%M, nc=((u128)c*x+(u128)d*z)%M, nd=((u128)c*y+(u128)d*w)%M; a=na;b=nb;c=nc;d=nd; }
    u64 nx=((u128)x*x+(u128)y*z)%M, ny=((u128)x*y+(u128)y*w)%M, nz=((u128)z*x+(u128)w*z)%M, nw=((u128)z*y+(u128)w*w)%M; x=nx;y=ny;z=nz;w=nw; n>>=1; }
  return b; /* Q^n = [[F_{n+1},F_n],[F_n,F_{n-1}]] */
}
int main(int c,char**v){ u64 hi=strtoull(v[1],0,10); long long tA=atoll(v[2]),tB=atoll(v[3]);
  u64 lo0 = c>4 ? strtoull(v[4],0,10) : 5; if(!(lo0&1)) lo0++; for(u64 m=lo0;m<hi;m+=2){ long long t=(m%3==0)?tB:tA; long long r=((long long)(t% (long long)m)+(long long)m)%(long long)m;
    if((fibmod(m,m)+ (u64)r)%m==0) printf("%llu\n",(unsigned long long)m);} return 0; }
