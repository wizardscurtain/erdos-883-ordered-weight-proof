#!/usr/bin/env python3
"""Bounded, deterministic tests; these do not replay the complete all-n archive."""
import argparse
import itertools
import json
import math
import platform
import random
import time
from pathlib import Path
import numpy as np
from integer_replay import arrays, kappa_all, count_le, le_exact, ceil_scaled_square, check_n

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, help='Optional path for a NEW test receipt')
options=parser.parse_args()
if options.output and options.output.exists():
    parser.error('Output exists; preserve the old receipt and choose a new path')
start=time.monotonic()
counts={}
data=arrays(100_000)
rad, phi, omega=data
kchecks=0
for x in [2_000, 10_000, 50_000]:
    kap,_=kappa_all(rad,phi,omega,x)
    for f,r,w,k in zip(phi,rad,omega,kap):
        assert le_exact(f,r,w,x,int(k),x)
        assert int(k)==0 or not le_exact(f,r,w,x,int(k)-1,x)
        kchecks+=1
counts['kappa_minimality_rows']=kchecks
cchecks=0
for x in [2_000, 50_000]:
    for P,Q in [(0,1),(1,3),(2,3),(1,1),(4,1)]:
        actual,_=count_le(rad,phi,omega,x,P,Q)
        expected=sum(le_exact(f,r,w,x,P,Q) for f,r,w in zip(phi,rad,omega))
        assert actual==expected,(x,P,Q,actual,expected)
        cchecks+=len(rad)
counts['threshold_comparisons_against_exact_oracle']=cchecks
rng=random.Random(883)
for _ in range(10_000):
    x=rng.randint(1,100_000_000); w=rng.randrange(1<<32)
    got=int(ceil_scaled_square(np.array([w],dtype=np.int64),x)[0])
    den=1<<64
    want=(x*w*w+den-1)//den
    assert got==want
counts['wide_product_limb_checks']=10_000
# Perfect-square inputs test inclusive equality in the polynomial predicate.
eq=0
for k in range(1,40):
    x=2*k*k
    for r in range(1,30):
        for f in range(1,r+1):
            for w in range(4):
                num=2*k*f-r*(1<<w); den=2*k*r
                if num<0: continue
                assert le_exact(f,r,w,x,num*num,den*den)
                if num:
                    assert not le_exact(f,r,w,x,num*num*2-1,den*den*2)
                eq+=1
counts['inclusive_equality_cases']=eq
# Marked gaps: endpoint flags arbitrary, low-weight middle is a suffix.
gaps=0
for ell in range(1,101):
    for low_middle in range(ell):
        for left,right in itertools.product([0,1],repeat=2):
            flags=[left]+[0]*(ell-1-low_middle)+[1]*low_middle+[right]
            c=sum(flags)
            marked=sum(bool(flags[i] or flags[i+1]) for i in range(ell))
            assert marked<=c+int(c>0)
            gaps+=1
counts['marked_gap_configurations']=gaps
# Abstract reserve claim, exhaustive lists over four resources up to length 3.
resources=set(range(4)); subsets=[set(c) for r in range(1,5)
                                  for c in itertools.combinations(resources,r)]
reserve_checks=0
for ell in [1,2,3]:
    for lists in itertools.product(subsets,repeat=ell):
        lists=sorted(lists,key=len)
        for reserve in range(3):
            if not all(len(L)>=j+1+reserve for j,L in enumerate(lists)): continue
            for r in range(reserve+1):
                for deletion in itertools.combinations(resources,r):
                    used=set(deletion)
                    for L in lists:
                        choices=L-used; assert choices
                        used.add(min(choices))
                    reserve_checks+=1
counts['reserve_deletion_configurations']=reserve_checks
# A transparent illustration of the actual construction at n=18.
A=set(range(1,14)); skeleton=[1,13,11,7]; cycle=[1,2,13,4,11,6,7]
assert len(set(cycle))==7 and set(cycle)<=A
assert all(math.gcd(cycle[i],cycle[(i+1)%7])==1 for i in range(7))
counts['worked_example_cycles']=1
points=[]
expected={4000:True,4025:False,4029:False,4035:False,4100:True,10000:True,30000:True}
for n, ok in expected.items():
    result=check_n(n,data)
    assert result['criterion_ok']==ok,(n,result)
    points.append(result)
report={'status':'PASS','scope':'bounded new tests, not a full historical evidence replay',
        'python':platform.python_version(),'numpy':np.__version__,
        'counts':counts,'point_results':points,'seconds':time.monotonic()-start}
if options.output:
    options.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
