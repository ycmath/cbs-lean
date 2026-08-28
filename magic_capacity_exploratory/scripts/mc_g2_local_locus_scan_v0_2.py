from __future__ import annotations
import csv, json, math, sys
from pathlib import Path
import numpy as np
from numba import njit

@njit
def idx(p,q,x):
    return (q*x+p-1)//p

@njit
def defect(p,h,q,x):
    return idx(h,q,idx(p,h,x))-idx(p,q,x)

@njit
def residual(p,a,x):
    return p*idx(p,a,x)-a*x

@njit
def audit_criterion(P,H,Q):
    triples=0; mismatch=0
    first=np.zeros(7,dtype=np.int64); maxdef=0
    for p in range(1,P+1):
        for h in range(1,H+1):
            for q in range(1,Q+1):
                triples += 1
                for x in range(p):
                    d=defect(p,h,q,x)
                    rh=residual(p,h,x); rq=residual(p,q,x)
                    crit=(q*rh <= h*rq)
                    if (d==0) != crit:
                        mismatch += 1
                        if first[0]==0:
                            first[:] = np.array([p,h,q,x,d,rh,rq])
                    if d>maxdef: maxdef=d
    return triples,mismatch,first,maxdef

@njit
def audit_scaling(P,H,Q):
    mismatch=0; first=np.zeros(4,dtype=np.int64)
    ds=np.array([2,3,5],dtype=np.int64)
    for p in range(1,P+1):
        for h in range(1,H+1):
            for q in range(1,Q+1):
                for di in range(len(ds)):
                    d=ds[di]
                    for x in range(p):
                        if defect(p,h,q,x)!=defect(d*p,d*h,d*q,x):
                            mismatch+=1
                            if first[0]==0: first[:]=np.array([p,h,q,d])
                            break
    return mismatch,first

def local_magic_set(p,h,q):
    return {x for x in range(p) if defect(p,h,q,x)==0}

def pascal_initial_row_mod(n,k,m):
    return [math.comb(n,j)%m if j<=n else 0 for j in range(k+1)]

def pascal_step(row,m):
    out=row[:]
    for j in range(len(out)-1,0,-1):
        out[j]=(row[j]+row[j-1])%m
    return out

def cbs_joint_period(p,k,max_steps=10_000_000):
    row=pascal_initial_row_mod(k,k,p)
    initial=tuple(row); period=0
    while True:
        period += 1; row=pascal_step(row,p)
        if tuple(row)==initial: return period
        if period>=max_steps: raise RuntimeError((p,k,"period cap"))

def cbs_cycle(p,k):
    T=cbs_joint_period(p,k)
    row=pascal_initial_row_mod(k,k,p)
    states=[]; trans=[]
    for _ in range(T):
        states.append(row[k]%p); trans.append(row[k-1]%p)
        row=pascal_step(row,p)
    return T,states,trans

def min_period(seq):
    n=len(seq)
    for d in range(1,n+1):
        if n%d==0 and all(seq[i]==seq[i%d] for i in range(n)):
            return d
    return n

def cyclic_max_false_gap(bits):
    if not any(bits): return None
    n=len(bits); best=cur=0
    for v in bits+bits:
        if not v: cur+=1; best=max(best,cur)
        else: cur=0
    return min(best,n-1)

def main(outdir):
    out=Path(outdir); out.mkdir(parents=True,exist_ok=True)
    audit_criterion(2,2,2); audit_scaling(2,2,2)
    triples,mismatch,first,maxdef=audit_criterion(64,128,64)
    smismatch,sfirst=audit_scaling(32,64,32)
    triples_rep=[
        (5,7,8,"coprime-gap"),(4,6,8,"common-factor-local"),
        (8,12,16,"scaled-common-factor-local"),(7,5,9,"other-local"),
        (7,11,9,"other-local-2")]
    ks=[2,3,4,5,8,16]; rows=[]
    for p,h,q,label in triples_rep:
        E=local_magic_set(p,h,q)
        for k in ks:
            T,sres,tres=cbs_cycle(p,k); joint=list(zip(sres,tres))
            ps=min_period(sres); pt=min_period(tres); pj=min_period(joint)
            sbit=[r in E for r in sres]; tbit=[r in E for r in tres]
            bbit=[a and b for a,b in zip(sbit,tbit)]
            rows.append({"label":label,"p":p,"h":h,"q":q,"k":k,"E":sorted(E),
                "pascal_orbit_period":T,"state_period":ps,"transition_period":pt,
                "joint_period":pj,"state_density":sum(sbit)/T,
                "transition_density":sum(tbit)/T,"bi_density":sum(bbit)/T,
                "state_max_wait":cyclic_max_false_gap(sbit),
                "transition_max_wait":cyclic_max_false_gap(tbit),
                "bi_max_wait":cyclic_max_false_gap(bbit),
                "coarse_bound_p_kfact":p*math.factorial(k),
                "period_divides_coarse_bound":(p*math.factorial(k))%T==0})
    cols=list(rows[0].keys())
    with (out/"cbs_period_density_gap.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=cols); w.writeheader(); w.writerows(rows)
    summary={"criterion_grid":{"p_max":64,"h_max":128,"q_max":64,
        "triples":int(triples),"mismatches":int(mismatch),
        "first_mismatch":first.tolist(),"max_defect":int(maxdef)},
        "scaling_grid":{"p_max":32,"h_max":64,"q_max":32,
        "mismatches":int(smismatch),"first_mismatch":sfirst.tolist()},
        "period_rows":len(rows),"all_pascal_periods_divide_p_times_k_factorial":
        all(r["period_divides_coarse_bound"] for r in rows)}
    (out/"summary.json").write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary,indent=2))

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else ".")
