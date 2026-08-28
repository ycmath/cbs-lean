from __future__ import annotations
import itertools, json, math, sys, time
from collections import defaultdict
from pathlib import Path
from statistics import mean, median
import numpy as np
import pandas as pd

SEED=20260829

def I(p,q,x): return (q*x+p-1)//p
def d(p,h,q,x): return I(h,q,I(p,h,x))-I(p,q,x)

def factors(n):
    z=[]; a=2
    while a*a<=n:
        if n%a==0:
            e=0
            while n%a==0:n//=a;e+=1
            z.append((a,e))
        a += 1 if a==2 else 2
    if n>1:z.append((n,1))
    return z
def flog(k,p):
    e=0
    while k>=p:k//=p;e+=1
    return e
def period(m,r):
    if r==0:return 1
    z=1
    for p,e in factors(m):z*=p**(e+flog(r,p))
    return z
def Tcycle(p,k):
    return [math.comb(k+L-1,k-1)%p for L in range(period(p,k-1))]

def waits(defects,b):
    ok=[v<=b for v in defects]; n=len(ok); ws=[]; paid=[]
    for s in range(n):
        w=0
        while not ok[(s+w)%n]:w+=1
        ws.append(w);paid.append(defects[(s+w)%n])
    ss=sorted(ws); tail=ss[math.floor(.95*n):]
    return dict(mean_wait=mean(ws),max_wait=max(ws),
                p95_wait=ss[math.ceil(.95*n)-1],cvar95_wait=mean(tail),
                mean_defect=mean(paid),density=sum(ok)/n)

def path_scan():
    out=[]
    for length,wmax in [(4,16),(5,10)]:
        paths=points=inter=absorbed=persist=endpoint=gep=gep_bad=0; mx=0
        by=defaultdict(lambda:[0,0])
        for w in itertools.product(range(1,wmax+1),repeat=length):
            paths+=1; all_end=True; all_prefix=True
            for x in range(w[0]):
                points+=1;y=x;ds=[0]
                for j in range(1,length):
                    y=I(w[j-1],w[j],y);ds.append(y-I(w[0],w[j],x))
                im=max(ds[1:-1],default=0); ed=ds[-1]
                all_end &= ed==0; all_prefix &= all(v==0 for v in ds[1:])
                endpoint += ed==0
                if im>0:
                    inter+=1
                    cls="compression" if w[-1]<w[-2] else "equal" if w[-1]==w[-2] else "expansion"
                    by[cls][1]+=1
                    if ed==0: absorbed+=1;by[cls][0]+=1;mx=max(mx,im)
                    else:persist+=1
            if all_end:gep+=1;gep_bad += not all_prefix
        out.append(dict(length=length,width_max=wmax,paths=paths,points=points,
                        intermediate=inter,absorbed=absorbed,
                        absorption=absorbed/inter,persistent=persist,
                        endpoint_exact=endpoint,global_endpoint_paths=gep,
                        global_endpoint_not_prefix=gep_bad,
                        global_not_prefix_fraction=gep_bad/gep,
                        max_absorbed=mx,
                        by_final_class={k:v[0]/v[1] for k,v in by.items()}))
    return out

def scheduler():
    cycles={(p,k):Tcycle(p,k) for p in range(2,25) for k in [2,3,4,5,8,16]}
    rows=[]; winners={r:defaultdict(int) for r in [.1,.25,.5,1,2,4,10]}
    for p in range(2,25):
      for q in range(1,25):
       for h in range(1,49):
        if all(d(p,h,q,x)==0 for x in range(p)):continue
        for k in [2,3,4,5,8,16]:
            raw=[d(p,h,q,x) for x in cycles[p,k]]; m=max(raw)
            pol={b:waits(raw,b) for b in sorted(set([0,1,2,m]))}
            for name,b in [("exact",0),("reserve1",1),("reserve2",2),("immediate",m)]:
                rows.append(dict(p=p,h=h,q=q,k=k,policy=name,budget=b,maxdef=m,
                                 immediate=b>=m,**pol[b]))
            for r in winners:
                b=min(pol,key=lambda b:(r*pol[b]["mean_wait"]+pol[b]["mean_defect"],b))
                winners[r]["exact" if b==0 else "reserve1" if b==1 else "reserve2" if b==2 else "immediate"]+=1
    f=pd.DataFrame(rows)
    s=f.groupby("policy").agg(rows=("p","size"),mean_wait=("mean_wait","mean"),
        mean_max_wait=("max_wait","mean"),mean_defect=("mean_defect","mean"),
        density=("density","mean"),fraction_immediate=("immediate","mean")).reset_index()
    reg=f.assign(regime=np.where(f.h>=f.q,"h>=q","h<q")).groupby(["regime","policy"]).agg(
        rows=("p","size"),mean_wait=("mean_wait","mean"),
        mean_max_wait=("max_wait","mean"),mean_defect=("mean_defect","mean"),
        density=("density","mean"),fraction_immediate=("immediate","mean")).reset_index()
    win=[]
    for r,c in winners.items():
        n=sum(c.values())
        for name in ["exact","reserve1","reserve2","immediate"]:
            win.append(dict(lambda_=r,policy=name,count=c[name],fraction=c[name]/n))
    return s,reg,pd.DataFrame(win)

def req(a,b,j):return a*(j-1)//b+1
def direct_times(p,q,x,sp=1.,tt=1.):
    B=I(p,q,x);S=[0.]+[i*sp for i in range(1,x+1)];D=[0.]*(B+1)
    for j in range(1,B+1):D[j]=max(S[req(p,q,j)],D[j-1])+tt
    return D
def insert_times(p,h,q,x,tm,sp=1.,tt=1.):
    A=I(p,h,x);C=I(h,q,A);S=[0.]+[i*sp for i in range(1,x+1)]
    M=[0.]*(A+1)
    for i in range(1,A+1):M[i]=max(S[req(p,h,i)],M[i-1])+tm
    Z=[0.]*(C+1)
    for j in range(1,C+1):
        cr=req(p,q,j); guard=S[cr] if cr<=x else 0.
        Z[j]=max(M[req(h,q,j)],guard,Z[j-1])+tt
    return M,Z
def maxplus():
    rows=[]
    for p in range(1,17):
     for h in range(1,17):
      for q in range(1,17):
       for x in range(1,p+1):
        B=I(p,q,x);C=I(h,q,I(p,h,x));dd=C-B;D=direct_times(p,q,x)
        for tm in [.25,.5,1.,2.]:
            M,Z=insert_times(p,h,q,x,tm)
            rows.append(dict(tm=tm,defect=dd,valid=Z[B]-D[B],
                             tail=Z[C]-Z[B],work=(len(M)-1)+C-B))
    f=pd.DataFrame(rows);out=[]
    for tm,g in f.groupby("tm"):
        out.append(dict(tm=tm,rows=len(g),
          corr_valid=g[["defect","valid"]].corr().iloc[0,1],
          spearman_valid=g[["defect","valid"]].corr(method="spearman").iloc[0,1],
          corr_tail=g[["defect","tail"]].corr().iloc[0,1],
          corr_work=g[["defect","work"]].corr().iloc[0,1],
          defect0_work=g[g.defect==0].work.mean(),
          defect0_valid=g[g.defect==0].valid.mean()))
    return pd.DataFrame(out)

def generators(r):
    I0=np.eye(r,dtype=np.int64);g=[]
    for i in range(r):
     for j in range(i+1,r):
      for a in [-1,1]:
       z=I0.copy();z[i,j]=a;g.append(z)
    return g
def invU(S):
    r=len(S);I0=np.eye(r,dtype=np.int64);N=S-I0;z=I0.copy();p=I0.copy();sg=-1
    for _ in range(1,r):p=p@N;z+=sg*p;sg*=-1
    return z
def candidates(r=4):
    G=generators(r);I0=np.eye(r,dtype=np.int64);D={I0.tobytes():I0}
    for a in G:D[a.tobytes()]=a
    for a in G:
     for b in G:
      z=b@a;D[z.tobytes()]=z
    return list(D.values())
def fullrank(rng,a,b,rank,density=.35):
    while True:
        z=((rng.random((a,b))<density)*rng.choice([-1,1],(a,b))).astype(np.int64)
        if np.linalg.matrix_rank(z.astype(float))>=rank:return z
def met(P,Q):
    return dict(nnz=np.count_nonzero(P)+np.count_nonzero(Q),
                l1=np.abs(P).sum()+np.abs(Q).sum(),
                mx=max(np.abs(P).max(initial=0),np.abs(Q).max(initial=0)))
def dom(a,b):return all(a[k]<=b[k] for k in ["nnz","l1","mx"]) and any(a[k]<b[k] for k in ["nnz","l1","mx"])
def lifting():
    rng=np.random.default_rng(SEED);C=candidates();rows=[]
    def evalone(i,suite,P,Q):
        K=Q@P;base=met(P,Q);best=None;nd=0;fail=0
        for S in C:
            Pi=S@P;Qi=Q@invU(S)
            if not np.array_equal(Qi@Pi,K):fail+=1;continue
            m=met(Pi,Qi);m["cond"]=np.linalg.cond(S.astype(float));nd+=dom(m,base)
            key=(m["nnz"],m["l1"],m["mx"],m["cond"])
            if best is None or key<best[0]:best=(key,m)
        rows.append(dict(suite=suite,fail=fail,dominated=nd>0,
                         reduction=base["nnz"]-best[1]["nnz"],
                         best_beats_direct=best[1]["nnz"]<np.count_nonzero(K),
                         best_cond=best[1]["cond"]))
    for i in range(64):evalone(i,"random",fullrank(rng,4,8,4),fullrank(rng,8,4,4))
    G=generators(4)
    for i in range(64):
        P0=fullrank(rng,4,8,4,.25);Q0=fullrank(rng,8,4,4,.25)
        first=G[rng.integers(len(G))]
        second=G[rng.integers(len(G))]
        R=second@first
        evalone(i,"structured_scrambled",R@P0,Q0@invU(R))
    f=pd.DataFrame(rows)
    return f.groupby("suite").agg(instances=("suite","size"),failures=("fail","sum"),
      fraction_dominated=("dominated","mean"),mean_nnz_reduction=("reduction","mean"),
      median_nnz_reduction=("reduction","median"),
      fraction_beats_direct=("best_beats_direct","mean"),mean_condition=("best_cond","mean")).reset_index()

def affine_metrics(p,E,a):
    return waits([0 if (a*t)%p in E else 1 for t in range(p)],0)
def ideal(T,M):
    F=T-M;q,r=divmod(F,M)
    return ((M-r)*q*(q+1)/2+r*(q+1)*(q+2)/2)/T,q+(1 if r else 0)
def baseline():
    rows=[]
    for p in range(2,25):
     U=[a for a in range(1,p) if math.gcd(a,p)==1]
     for q in range(1,25):
      for h in range(1,49):
       E={x for x in range(p) if d(p,h,q,x)==0}
       if len(E)==p:continue
       lin=affine_metrics(p,E,1);best=min((affine_metrics(p,E,a) for a in U),
          key=lambda m:(m["max_wait"],m["mean_wait"]))
       for k in [2,3,4,5,8,16]:
        cyc=Tcycle(p,k);m=waits([0 if x in E else 1 for x in cyc],0)
        im,ix=ideal(len(cyc),round(m["density"]*len(cyc)))
        rows.append(dict(k=k,E=len(E)/p,cbs=m["density"],cbs_mean=m["mean_wait"],
          cbs_max=m["max_wait"],lin_max=lin["max_wait"],aff_max=best["max_wait"],
          ideal_mean=im,ideal_max=ix))
    f=pd.DataFrame(rows);out=[]
    for k,g in f.groupby("k"):
        out.append(dict(k=k,rows=len(g),density_adv=(g.cbs-g.E).mean(),
          density_gt=(g.cbs>g.E).mean(),better_aff=(g.cbs_max<g.aff_max).mean(),
          equal_aff=(g.cbs_max==g.aff_max).mean(),worse_aff=(g.cbs_max>g.aff_max).mean(),
          max_excess=(g.cbs_max-g.ideal_max).mean(),
          mean_excess=(g.cbs_mean-g.ideal_mean).mean()))
    return pd.DataFrame(out)

def main(out="."):
    out=Path(out);out.mkdir(parents=True,exist_ok=True);t=time.time()
    result={"seed":SEED,"path":path_scan()}
    s,r,w=scheduler();s.to_csv(out/"scheduler_summary.csv",index=False)
    r.to_csv(out/"scheduler_regime.csv",index=False);w.to_csv(out/"scheduler_winners.csv",index=False)
    maxplus().to_csv(out/"maxplus_summary.csv",index=False)
    lifting().to_csv(out/"lifting_summary.csv",index=False)
    baseline().to_csv(out/"baseline_summary.csv",index=False)
    result["elapsed_s"]=time.time()-t
    (out/"summary.json").write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

if __name__=="__main__":main(sys.argv[1] if len(sys.argv)>1 else ".")
