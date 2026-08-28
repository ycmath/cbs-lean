from __future__ import annotations
import csv, json, math, sys
from pathlib import Path

def prime_factorization(n):
    out=[]; d=2
    while d*d<=n:
        if n%d==0:
            a=0
            while n%d==0:
                n//=d; a+=1
            out.append((d,a))
        d += 1 if d==2 else 2
    if n>1: out.append((n,1))
    return out

def floor_log_prime(k, prime):
    e=0
    while k >= prime:
        k//=prime; e+=1
    return e

def kwong_binomial_period(modulus, lower_index):
    if lower_index == 0: return 1
    T=1
    for prime,a in prime_factorization(modulus):
        T *= prime ** (a + floor_log_prime(lower_index, prime))
    return T

def row_initial(n,k,m):
    return [math.comb(n,j)%m if j<=n else 0 for j in range(k+1)]

def step(row,m):
    out=row[:]
    for j in range(len(row)-1,0,-1): out[j]=(row[j]+row[j-1])%m
    return out

def observed_period(modulus,k):
    predicted=kwong_binomial_period(modulus,k)
    seq=[]; row=row_initial(k,k,modulus)
    for _ in range(predicted):
        seq.append(row[k]); row=step(row,modulus)
    if row[k] != seq[0]: return None,predicted
    for d in range(1,predicted+1):
        if predicted%d==0 and all(seq[i]==seq[i%d] for i in range(predicted)):
            return d,predicted
    return predicted,predicted

def main(outdir):
    out=Path(outdir); out.mkdir(parents=True,exist_ok=True)
    rows=[]; mismatches=[]
    for m in range(2,65):
        for k in range(1,33):
            obs,pred=observed_period(m,k); ok=(obs==pred)
            rows.append((m,k,obs,pred,ok))
            if not ok: mismatches.append((m,k,obs,pred))
    with (out/"kwong_period_audit.csv").open("w",newline="") as f:
        w=csv.writer(f); w.writerow(["modulus","lower_index","observed_period","kwong_period","match"]); w.writerows(rows)
    summary={"pairs":len(rows),"mismatch_count":len(mismatches),"first_mismatches":mismatches[:10]}
    (out/"kwong_period_audit_summary.json").write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary,indent=2))

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else ".")
