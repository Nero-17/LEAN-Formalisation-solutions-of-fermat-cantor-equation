"""Floating full-phase discovery for one fixed M=3^m, with graph bands."""
import json
import math
import time
import argparse
from functools import lru_cache
from pathlib import Path
import numpy as np
from alln20261020_inner_phase_probe import prefixes, modular_gaps

BASE=[(11/9,2027/1624),(11/7,21/11),
      (89/73,171/137),(101/79,183/143),(89/57,171/89),
      (143/61,237/101),(137/57,219/89)]
BANDS=BASE+[(1/b,1/a) for a,b in BASE]

@lru_cache(maxsize=128)
def geometry(m,P,endpoint_depth,height,depth):
    M=3.**m
    u=P/3.**endpoint_depth
    center=3.**height/2
    v=(2+prefixes(depth))/3
    vw=3.**(-depth-1)
    result=[]
    for p in range(max(0,depth+height-2),depth+height+4):
        aw=3.**(height-p)
        a=3.**height*prefixes(p)
        rlo=aw*v[None,:]/((u+(a[:,None]+aw)/M)*vw)
        rhi=aw*(v[None,:]+vw)/((u+a[:,None]/M)*vw)
        phi_lower=M*np.log1p((center-a-aw)/(M*u+a+aw))
        phi_upper=M*np.log1p((center-a)/(M*u+a))
        result.append((rlo,rhi,phi_lower[:,None],phi_upper[:,None],
                       np.log(v)[None,:],np.log(v+vw)[None,:]))
    return result

def good_interval(tlo,thi,m,P,endpoint_depth=6,height=3,depth=4,inset=1e-9):
    lower,upper=[],[]
    for rlo,rhi,pl,pu,lv,uv in geometry(m,P,endpoint_depth,height,depth):
        good=np.zeros_like(rlo,dtype=bool)
        for lo,hi in BANDS:
            good|=(tlo*rlo>lo)&(thi*rhi<hi)
        if not np.any(good):continue
        left=(lv+np.where(pl>=0,thi,tlo)*pl)/math.log(3)+inset
        right=(uv+np.where(pu>=0,tlo,thi)*pu)/math.log(3)-inset
        good&=left<right
        lower.extend(left[good]);upper.extend(right[good])
    return not modular_gaps(lower,upper)

def discover(m,step=1000,broad=False):
    started=time.monotonic()
    old=json.loads(Path("work/alln20261020_selected_cover.json").read_text()) if broad else None
    endpoint_depth=9 if broad else 6
    endpoints=list(dict.fromkeys([r["P"] for r in old["t_cover"]]+
                    [round(float(x)*19683) for x in prefixes(6) if x>=2/3-1e-12])) if broad else [
                    round(float(x)*729) for x in prefixes(6) if x>=2/3-1e-12]
    recent=endpoints.copy()
    cells=[]
    failures=[]
    stack=[(k,step,0) for k in range(2*step-1,step-1,-1)]
    while stack:
        k,den,level=stack.pop()
        lo,hi=k/den,(k+1)/den
        chosen=None
        preferred=([r["P"] for r in old["t_cover"] if r["t_interval"][0]<=(lo+hi)/2<=r["t_interval"][1]]
                   if broad else [])
        order=list(dict.fromkeys(preferred+recent))
        for P in order:
            if good_interval(lo,hi,m,P,endpoint_depth):
                chosen=P;break
        if chosen is not None:
            cells.append({"t_lower":[k,den],"t_upper":[k+1,den],"P":chosen})
            recent.remove(chosen);recent.insert(0,chosen)
        elif level<8:
            stack.extend([(2*k+1,2*den,level+1),(2*k,2*den,level+1)])
        else:
            failures.append([lo,hi])
        if len(cells) and len(cells)%200==0:
            Path(f"work/alln20261020_fixed_m{m}_lower_progress.json").write_text(json.dumps(dict(cells=cells,failures=failures,stack=stack)))
            print(m,len(cells),len(stack),len(failures),round(time.monotonic()-started,1),flush=True)
    result={"status":"floating candidate only","m":m,"endpoint_depth":endpoint_depth,"height":3,
            "v_depth":4,"inset":1e-9,"cells":cells,"failures":failures,
            "elapsed_seconds":time.monotonic()-started}
    Path(f"work/alln20261020_fixed_m{m}_lower_candidate.json").write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ("cells","failures")}|
                     {"cell_count":len(cells),"failure_count":len(failures)},indent=2))
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--m",type=int,required=True)
    parser.add_argument("--step",type=int,default=1000)
    parser.add_argument("--broad",action="store_true")
    args=parser.parse_args()
    discover(args.m,args.step,args.broad)
