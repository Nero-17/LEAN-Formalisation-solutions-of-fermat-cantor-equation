"""Exploratory finite-depth cylinder counts, not a dimension proof."""
import numpy as np
import math, json, time, argparse
from pathlib import Path
from fractions import Fraction

def candidate_m(n,lam,k):
    xlo=lam**k*(1-lam)
    xhi=min(lam**k,2**(-1/n))
    if xlo>xhi:return range(0)
    vlo=-math.expm1(math.log1p(-xlo**n)/n)
    vhi=-math.expm1(math.log1p(-xhi**n)/n)
    lo=max(1,math.ceil(math.log(vhi/(1-lam))/math.log(lam)-1e-10))
    hi=math.floor(math.log(vlo)/math.log(lam)+1e-10)
    return range(lo,hi+1)

def evaluate(n,lam,depth=20,kmax=6):
    best=-1.; best_count=0; best_pair=None; capped=False
    for k in range(kmax+1):
        for m in candidate_m(n,lam,k):
            r=local_counts(n,lam,k,m,depth,1200)
            if r['counts'][-1]:
                s=r['slope'] if r['slope'] is not None else -1.
                if s>best:best=s;best_count=r['counts'][-1];best_pair=[k,m];capped=r['capped']
                # Strong observed growth in one compact cylinder suffices for
                # the numerical positive classification, not for a theorem.
                if s>.08 and r['counts'][-1]>=12:
                    return {'slope':s,'count':r['counts'][-1],'pair':[k,m],'capped':r['capped'],'low_growth':False}
    return {'slope':max(0.,best),'count':best_count,'pair':best_pair,'capped':capped,
            'low_growth':best<.025 or best_count<8}

def local_counts(n, lam, k, m, depth=20, cap=5000):
    # Actual right-first cylinders x=lambda^k X, v=lambda^m Y.
    # X,Y in (1-lambda)+lambda C; work with their tail coordinates.
    a=np.array([0.]); b=np.array([0.]); w=1.
    def residual(a,b):
        X=1-lam+lam*a; Y=1-lam+lam*b
        z=lam**m*Y
        with np.errstate(divide='ignore',invalid='ignore'):
            correction=np.log(-np.expm1(n*np.log1p(-z))/(n*z))
        return (n*k-m)*math.log(lam)+n*np.log(X)-math.log(n)-np.log(Y)-correction
    result=[]
    for level in range(depth+1):
        lo=residual(a,np.minimum(1.,b+w)); hi=residual(np.minimum(1.,a+w),b)
        keep=(lo<=2e-14)&(hi>=-2e-14)&(lam**k*(1-lam+lam*a)+lam**m*(1-lam+lam*b)<=1.+2e-14)
        a=a[keep]; b=b[keep]; result.append(len(a))
        if len(a)==0 or len(a)>=cap or level==depth:break
        shift=(1-lam)*w
        a=np.concatenate((a,a,a+shift,a+shift)); b=np.concatenate((b,b+shift,b,b+shift)); w*=lam
    d=len(result)-1
    slope=None
    if d>=8 and result[-1]>0:
        slope=float(np.polyfit(np.arange(d-6,d+1),np.log(result[d-6:d+1]),1)[0]/math.log(1/lam))
    return {'k':k,'m':m,'counts':result,'slope':slope,'capped':result[-1]>=cap}

def local_scan(n,lam,depth=20,kmax=6,cap=5000):
    out=[]
    for k in range(kmax+1):
        for m in candidate_m(n,lam,k):
            r=local_counts(n,lam,k,m,depth,cap)
            if r['counts'][0]:out.append(r)
    return out

def counts(n, lam, depth=26, cap=30000):
    # Reflect y: v=1-y is again in C_lambda. Solve x^n=1-(1-v)^n.
    # Logarithms and expm1 avoid cancellation at the persistent endpoint (0,0).
    x=np.array([0.]); v=np.array([0.]); width=1.
    result=[1]
    for level in range(1,depth+1):
        shift=(1-lam)*width
        x=np.concatenate((x,x,x+shift,x+shift))
        v=np.concatenate((v,v+shift,v,v+shift))
        width*=lam
        with np.errstate(divide='ignore',invalid='ignore'):
            lx=n*np.log(x); ux=n*np.log(np.minimum(1.,x+width))
            lv=np.log(-np.expm1(n*np.log1p(-v)))
            uv=np.log(-np.expm1(n*np.log1p(-np.minimum(1.,v+width))))
        # Only the half arc x<=y; symmetry does not affect dimension.
        keep=(lx<=uv+2e-13)&(lv<=ux+2e-13)&(x+v<=1.+2e-14)
        x=x[keep]; v=v[keep]
        result.append(len(x))
        if len(x)>=cap: break
    slopes={}
    for d in [14,18,22,26]:
        if d<len(result):
            slopes[str(d)]=float(np.polyfit(np.arange(d-6,d+1),np.log(np.array(result[d-6:d+1])),1)[0]/math.log(1/lam))
    return {'counts':result,'slopes':slopes,'capped':len(result)<depth+1}

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--probe',action='store_true'); p.add_argument('--local-probe',action='store_true'); p.add_argument('--grid',action='store_true'); p.add_argument('--refine',action='store_true')
    args=p.parse_args()
    if args.probe:
        for n in [2,3,4,5,8,7/3]:
            for lam in [.26,.268,.28,.30,.304,.32,1/3,.34,.36,.38,.4,.45]:
                r=counts(n,lam)
                print(n,round(lam,6),r['counts'][-1],r['slopes'],r['capped'],flush=True)
    if args.local_probe:
        for n in [2,3,4,5,8,7/3]:
            for lam in [.26,.268,.28,.30,.304,.32,1/3,.34,.36,.38,.4,.45]:
                rs=local_scan(n,lam,18,6,2000)
                alive=[r for r in rs if r['counts'][-1]>0]
                best=max(alive,key=lambda r:r['slope'] or -1) if alive else None
                print(n,round(lam,6),'alive',len(alive),'best',best,flush=True)
    if args.grid:
        fs=sorted({Fraction(a,b) for b in range(1,4) for a in range(2*b,8*b+1)})
        target=Path(__file__).with_name('last-transition-grid.jsonl')
        done=set()
        if target.exists():
            done={row['n'] for row in map(json.loads,target.read_text().splitlines())}
        for frac in fs:
            if str(frac) in done:continue
            start=time.time(); rows=[]
            for j in range(125,251):
                lam=j/500
                if lam==.5:continue
                r=evaluate(float(frac),lam,20,6)
                rows.append({'lambda':lam,**r})
            low=[r['lambda'] for r in rows if r['low_growth']]
            result={'n':str(frac),'n_float':float(frac),'step':.002,'depth':20,'kmax':6,'rows':rows,
                    'last_low':max(low) if low else None,'seconds':time.time()-start}
            with target.open('a') as f:f.write(json.dumps(result)+'\n')
            print(str(frac),result['last_low'],round(time.time()-start,2),flush=True)
    if args.refine:
        target=Path(__file__).with_name('last-transition-refined.jsonl')
        done=set()
        if target.exists():done={row['n'] for row in map(json.loads,target.read_text().splitlines())}
        coarse=[json.loads(l) for l in Path(__file__).with_name('last-transition-grid.jsonl').read_text().splitlines()]
        for entry in coarse:
            if entry['n'] in done:continue
            start=time.time(); rows=[]
            # Scan the whole lower parameter region, including above the last
            # coarse low-growth point: positivity need not be monotone.
            for j in range(500,701):
                lam=j/2000
                r=evaluate(entry['n_float'],lam,22,12)
                rows.append({'lambda':lam,**r})
            low=[r['lambda'] for r in rows if r['low_growth']]
            result={'n':entry['n'],'n_float':entry['n_float'],'step':.0005,'depth':22,'kmax':12,'rows':rows,
                    'last_low':max(low) if low else None,'seconds':time.time()-start}
            with target.open('a') as f:f.write(json.dumps(result)+'\n')
            print(entry['n'],result['last_low'],round(time.time()-start,2),flush=True)
