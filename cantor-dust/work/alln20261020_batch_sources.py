"""Vectorised floating discovery; every result requires independent exact checks."""
from pathlib import Path
import argparse
import json
import math
import time
import numpy as np
from alln20261020_parent_logsource import prefixes, BANDS

def batch(ns,m,max_q=6):
    remaining=np.array(ns,dtype=np.int64)
    records=[]
    for endpoint_depth in (2,3,1,4,5,6):
        if endpoint_depth>m:
            continue
        endpoints=prefixes(endpoint_depth)
        endpoints=endpoints[endpoints>=2*3**(endpoint_depth-1)]
        for height in dict.fromkeys((min(2,m-endpoint_depth),min(3,m-endpoint_depth),0)):
            for q in range(2,max_q+1):
                vs=2*3**(q-1)+prefixes(q-1)
                for da in range(max(0,q+height-2),q+height+3):
                    p=m-height+da
                    if p<endpoint_depth:
                        continue
                    for endpoint in endpoints:
                        us=int(endpoint)*3**(p-endpoint_depth)+prefixes(da)
                        u=np.repeat(us,len(vs))
                        v=np.tile(vs,len(us))
                        rlow=v/(u+1)
                        rhigh=(v+1)/u
                        nmin,nmax=int(remaining[0]),int(remaining[-1])
                        allowed=np.zeros(len(u),dtype=bool)
                        for lo,hi in BANDS:
                            allowed|=(rlow*nmax>lo+1e-10)&(rhigh*nmin<hi-1e-10)
                        if not allowed.any():
                            continue
                        u,v,rlow,rhigh=(a[allowed] for a in (u,v,rlow,rhigh))
                        # Cap matrix memory for unusually deep discovery templates.
                        chunk=max(1,min(len(remaining),1000000//len(u)))
                        survived=[]
                        for offset in range(0,len(remaining),chunk):
                            current=remaining[offset:offset+chunk]
                            nr=current[:,None]
                            good=np.zeros((len(current),len(u)),dtype=bool)
                            for lo,hi in BANDS:
                                good|=(nr*rlow[None,:]>lo+1e-10)&(nr*rhigh[None,:]<hi-1e-10)
                            if not good.any():
                                survived.extend(current.tolist())
                                continue
                            lower=(nr*np.log(u[None,:]/3.**p)-np.log((v[None,:]+1)/3.**q)
                                   -np.log(nr))/math.log(3)
                            upper=(nr*np.log((u[None,:]+1)/3.**p)-np.log(v[None,:]/3.**q)
                                   -np.log(nr))/math.log(3)
                            target=np.floor(lower)+1
                            good &= target<upper-1e-9
                            found=good.any(axis=1)
                            for i in np.flatnonzero(found):
                                j=int(np.argmax(good[i]))
                                records.append(dict(n=int(current[i]),P=int(u[j]),p=p,
                                                    Q=int(v[j]),q=q,d=int(-target[i,j])))
                            survived.extend(current[~found].tolist())
                        remaining=np.array(survived,dtype=np.int64)
                        if not len(remaining):
                            return records,[]
    return records,remaining.tolist()

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--start",type=int,required=True)
    parser.add_argument("--end",type=int,required=True)
    parser.add_argument("--output",required=True)
    parser.add_argument("--batch-size",type=int,default=1000)
    args=parser.parse_args()
    started=time.monotonic()
    records=[]
    missing=[]
    begin=args.start
    batches=0
    while begin<=args.end:
        m=0
        while 3**(m+1)<=begin:
            m+=1
        end=min(begin+args.batch_size-1,3**(m+1)-1,args.end)
        found,absent=batch(range(begin,end+1),m)
        records.extend(found)
        missing.extend(absent)
        batches+=1
        if batches%10==0 or end==args.end:
            result=dict(status="floating discovery only",start=args.start,end=end,
                        found=len(records),missing=missing,seconds=time.monotonic()-started,
                        rows=sorted(records,key=lambda r:r["n"]))
            Path(args.output).write_text(json.dumps(result,separators=(",",":")))
            print({k:v for k,v in result.items() if k!="rows"},flush=True)
        begin=end+1
