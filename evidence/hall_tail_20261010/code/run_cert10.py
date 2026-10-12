import sys, json, cert10
SS=((5,7,11,13),(5,7,11),(5,7),(5,),(5,11),(5,7,13),(5,11,13),(7,11,13),())
lo,hi,out=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]
spf=cert10.spf_table(hi)
with open(out,'a') as fh:
    for n in range(lo,hi+1):
        u=cert10.coverage_multi(n,spf,full_grid=True,sigsets=SS)
        fh.write(json.dumps({"n":n,"m":n//6,"n_uncovered":len(u),"uncovered":[list(x) for x in u[:12]]})+"\n"); fh.flush()
