"""Finite outer-image test for the two-parameter endpoint limit.

Intervals enclose log(v)/log(3) - 3*t*a/(2*log(3)),
a in C, v in (2+C)/3. Float output is exploratory, not a proof.
"""
import json
import math
import numpy as np
from pathlib import Path

def prefixes(depth):
    points = np.array([0.0])
    for j in range(1, depth + 1):
        points = np.concatenate((points, points + 2 / 3**j))
    return points

def gaps(t, depth):
    left = prefixes(depth)
    width = 3.0**(-depth)
    lower = (np.log((2+left[None,:])/3) - 1.5*t*(left[:,None]+width))/math.log(3)
    upper = (np.log((2+left[None,:]+width)/3) - 1.5*t*left[:,None])/math.log(3)
    lower, upper = lower.ravel(), upper.ravel()
    shift = np.floor(lower)
    lower, upper = lower-shift, upper-shift
    wrap = upper > 1
    lower = np.concatenate((lower, np.zeros(np.sum(wrap))))
    upper = np.concatenate((np.minimum(upper,1), upper[wrap]-1))
    order = np.argsort(lower)
    lower, upper = lower[order], upper[order]
    running = np.maximum.accumulate(upper)
    indices = np.nonzero(lower[1:] > running[:-1])[0]
    holes = [(float(running[j]),float(lower[j+1])) for j in indices]
    if lower[0]>0: holes.insert(0,(0,float(lower[0])))
    if running[-1]<1: holes.append((float(running[-1]),1))
    return {"t":t,"depth":depth,"hole_count":len(holes),
            "max_gap":max((b-a for a,b in holes), default=0),
            "largest_gaps":sorted(holes,key=lambda pair:pair[1]-pair[0],reverse=True)[:3]}

if __name__ == "__main__":
    results=[]
    for t in [1,1.125,1.25,1.5,1.75,2,2.25,2.5,2.75,3]:
        for depth in [5,7,9]:
            result=gaps(t,depth)
            results.append(result)
            print(json.dumps(result),flush=True)
    Path(__file__).with_suffix(".json").write_text(
        json.dumps({"status":"floating-point outer-image probe only","results":results},indent=2))
