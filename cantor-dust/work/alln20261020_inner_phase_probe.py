"""Exploratory circle cover using source rectangles in proved slope bands.

No floating-point output is a certificate. The images of qualifying source
rectangles are intervals by the existing local covering lemma.
"""
import math
import json
from pathlib import Path
import numpy as np
from alln20261020_logphase_probe import prefixes
from functools import lru_cache

prefixes=lru_cache(None)(prefixes)

BANDS=[(11/9,2027/1624),(11/7,21/11)]
BANDS += [(1/b,1/a) for a,b in BANDS.copy()]

def modular_gaps(lower,upper):
    if not len(lower): return [(0.,1.)]
    lower,upper=np.asarray(lower),np.asarray(upper)
    shift=np.floor(lower)
    lower,upper=lower-shift,upper-shift
    wrap=upper>1
    lower=np.r_[lower,np.zeros(sum(wrap))]
    upper=np.r_[np.minimum(upper,1),upper[wrap]-1]
    order=np.argsort(lower)
    lower,upper=lower[order],upper[order]
    running=np.maximum.accumulate(upper)
    holes=[(float(running[j]),float(lower[j+1])) for j in
           np.nonzero(lower[1:]>running[:-1])[0]]
    if lower[0]>0: holes.insert(0,(0.,float(lower[0])))
    if running[-1]<1: holes.append((float(running[-1]),1.))
    return holes

def inner(t,endpoint,height=2,depth=4):
    coefficient=t/endpoint
    vlo=(2+prefixes(depth))/3
    vw=3.**(-depth-1)
    lower,upper=[],[]
    count=0
    for adepth in range(max(0,depth+height-2),depth+height+4):
        aw=3.**(height-adepth)
        ratios=coefficient*aw/vw
        good=np.zeros(len(vlo),dtype=bool)
        for lo,hi in BANDS:
            good |= (ratios*vlo>lo)&(ratios*(vlo+vw)<hi)
        selected=vlo[good]
        if not len(selected): continue
        a=3.**height*prefixes(adepth)
        lower.extend(((np.log(selected[None,:])-coefficient*(a[:,None]+aw))/math.log(3)).ravel())
        upper.extend(((np.log(selected[None,:]+vw)-coefficient*a[:,None])/math.log(3)).ravel())
        count+=len(a)*len(selected)
    holes=modular_gaps(lower,upper)
    return {"t":float(t),"endpoint":endpoint,"height":height,"depth":depth,
            "source_count":count,"gap_count":len(holes),
            "max_gap":max((b-a for a,b in holes),default=0),
            "largest_gaps":sorted(holes,key=lambda ab:ab[1]-ab[0],reverse=True)[:3]}

def robust_intervals(t, radius, endpoint, height=2, depth=4, inset=1e-10):
    """Intersection over |s-t|<=radius, after one harmless phase rotation."""
    vlo=(2+prefixes(depth))/3
    vw=3.**(-depth-1)
    lower,upper=[],[]
    center=3.**height/2
    for adepth in range(max(0,depth+height-2),depth+height+4):
        aw=3.**(height-adepth)
        ratios=aw/vw/endpoint
        good=np.zeros(len(vlo),dtype=bool)
        for lo,hi in BANDS:
            good |= (ratios*(t-radius)*vlo>lo)&(ratios*(t+radius)*(vlo+vw)<hi)
        selected=vlo[good]
        if not len(selected): continue
        a=3.**height*prefixes(adepth)
        alower=(center-a-aw)/endpoint
        aupper=(center-a)/endpoint
        lower.extend(((np.log(selected[None,:])+t*alower[:,None]
                       +radius*np.abs(alower[:,None]))/math.log(3)+inset).ravel())
        upper.extend(((np.log(selected[None,:]+vw)+t*aupper[:,None]
                       -radius*np.abs(aupper[:,None]))/math.log(3)-inset).ravel())
    return lower,upper

def robust_radius(t, endpoint, height=2, depth=4):
    if modular_gaps(*robust_intervals(t,0,endpoint,height,depth)):
        return 0.
    lo,hi=0.,.02
    for _ in range(19):
        mid=(lo+hi)/2
        if modular_gaps(*robust_intervals(t,mid,endpoint,height,depth)): hi=mid
        else: lo=mid
    return lo

if __name__=="__main__":
    records=[]
    for t in np.linspace(1,3,41):
        batch=[inner(t,u) for u in [2/3,8/9,512/729]]
        records.extend(batch)
        print(json.dumps({"t":float(t),"max_gaps":[r["max_gap"] for r in batch],
                          "some_full":any(r["gap_count"]==0 for r in batch)}),flush=True)
    Path(__file__).with_suffix(".json").write_text(json.dumps(
        {"status":"floating-point exploratory inner-image cover","records":records},indent=2))
