"""Brute-force check of refined costs: for small n, recompute lam3', lamA', lamN' by direct loops."""
import sys
from math import gcd
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fastcert, numpy as np
def pf(v):
    out,p=[],2
    while p*p<=v:
        if v%p==0:
            out.append(p)
            while v%p==0: v//=p
        p+=1
    if v>1: out.append(v)
    return out
ok=True
for n in map(int, sys.argv[1:]):
    for P in ((5,7,11,13),(5,7),(5,),()):
        D=fastcert.build_fast(n,P,refined=True)
        q=n//2
        base=[];cR=[]
        for v in range(1,n+1,2):
            ps=[p for p in pf(v) if p!=3]; S=[p for p in ps if p in P]; Lg=[p for p in ps if p not in P]
            pr=1
            for p in S: pr*=p
            if v%3==0:
                s3=sum(1 for k in range(1,q+1) if k%3 and gcd(k,pr)>1)
                l3=sum(sum(1 for k in range(1,q+1) if k%3 and k%p==0 and gcd(k,pr)==1) for p in Lg)
                base.append(s3+2*l3)
            else:
                sA=sum(1 for k in range(1,q+1) if gcd(k,pr)>1)
                lA=sum(sum(1 for k in range(1,q+1) if k%p==0 and gcd(k,pr)==1) for p in Lg)
                base.append(sA+2*lA)
                sN=sum(1 for u in range(1,n+1) if gcd(u,pr)>1)
                lN=sum(sum(1 for u in range(1,n+1) if u%p==0 and gcd(u,pr)==1) for p in Lg)
                cR.append(sN+2*lN)
        same = list(D['base'])==base and list(D['cR'])==cR
        ok &= same
        print(n,P,'MATCH' if same else 'MISMATCH')
print('LAMPRIME_CHECK_PASS' if ok else 'LAMPRIME_CHECK_FAIL')
