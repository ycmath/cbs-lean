from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np
from numba import njit

@njit
def idx(p, q, x):
    return (q*x + p - 1)//p

@njit
def defect(p, h, q, x):
    return idx(h, q, idx(p, h, x)) - idx(p, q, x)

@njit
def interval_contains(p, h, q, x):
    if x == 0:
        return True
    y = idx(p, q, x)
    lower = (p*(y-1))//q + 1
    a = (h*y)//q
    upper = (p*a)//h
    if upper >= p:
        upper = p - 1
    return lower <= x <= upper

@njit
def audit(P, H, Q):
    mismatch = 0
    first = np.zeros(7, dtype=np.int64)
    for p in range(1, P+1):
        for h in range(1, H+1):
            for q in range(1, Q+1):
                for x in range(p):
                    direct = defect(p,h,q,x) == 0
                    chamber = interval_contains(p,h,q,x)
                    if direct != chamber:
                        mismatch += 1
                        if first[0] == 0:
                            first[:] = np.array([p,h,q,x,int(direct),int(chamber),idx(p,q,x)])
    return mismatch, first

def main(outdir="."):
    out = Path(outdir); out.mkdir(parents=True, exist_ok=True)
    audit(2,2,2)
    mismatch, first = audit(96,192,96)
    summary = {"p_max":96,"h_max":192,"q_max":96,
        "triples":96*192*96,"mismatch_count":int(mismatch),
        "first_mismatch":first.tolist(),"seed":None}
    (out/"interval_decomposition_audit.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv)>1 else ".")
