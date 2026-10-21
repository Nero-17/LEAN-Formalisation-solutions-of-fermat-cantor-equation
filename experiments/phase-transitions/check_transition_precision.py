"""Higher precision finite-depth checks; not rigorous interval arithmetic."""
from pathlib import Path
from fractions import Fraction
import json,math,time
import sys
import mpmath as mp
import numpy as np
from scan_last_transition import candidate_m
mp.mp.dps=50
base=Path(__file__).parent

def local(n,lam,k,m,depth=None,cap=256):
    if depth is None:depth=52 if '--deep' in sys.argv else 34
    a=[(mp.mpf(0),mp.mpf(0))]; w=mp.mpf(1); counts=[]
    constant=(n*k-m)*mp.log(lam)-mp.log(n)
    scale=lam**m
    def res(x,y):
        X=1-lam+lam*x; Y=1-lam+lam*y; z=scale*Y
        return constant+n*mp.log(X)-mp.log(Y)-mp.log(-mp.expm1(n*mp.log1p(-z))/(n*z))
    for d in range(depth+1):
        a=[(x,y) for x,y in a if res(x,y+w)<=0 and res(x+w,y)>=0 and lam**k*(1-lam+lam*x)+scale*(1-lam+lam*y)<=1]
        counts.append(len(a))
        if not a or len(a)>=cap or d==depth:break
        s=(1-lam)*w; a=[(x+dx,y+dy) for x,y in a for dx,dy in [(0,0),(0,s),(s,0),(s,s)]]; w*=lam
    d=len(counts)-1
    slope=float(np.polyfit(np.arange(d-6,d+1),np.log(counts[d-6:d+1]),1)[0]/math.log(1/float(lam))) if d>=8 and counts[-1] else 0.
    return {'k':k,'m':m,'counts':counts,'slope':slope}

def evaluate(frac,lam):
    n=mp.mpf(frac.numerator)/frac.denominator; lm=mp.mpf(str(lam)); best=0.; bc=0; checked=[]; positive=False
    for k in range(13):
        for m in candidate_m(float(frac),lam,k):
            r=local(n,lm,k,m);checked.append(r)
            if r['slope']>best:best=r['slope'];bc=r['counts'][-1]
            if r['slope']>=.025 and r['counts'][-1]>=8:positive=True
            if r['slope']>.08 and r['counts'][-1]>=12:
                return {'low_growth':False,'slope':r['slope'],'checked':checked}
    return {'low_growth':not positive,'slope':best,'checked':checked}

if __name__=='__main__':
    refined={r['n']:r for r in map(json.loads,(base/'last-transition-refined.jsonl').read_text().splitlines())}
    deep='--deep' in sys.argv
    prior={r['n']:r for r in map(json.loads,(base/'last-transition-precision.jsonl').read_text().splitlines())} if deep else {}
    out=base/('last-transition-deep.jsonl' if deep else 'last-transition-precision.jsonl'); done=set()
    if out.exists():done={r['n'] for r in map(json.loads,out.read_text().splitlines())}
    for key,entry in refined.items():
        if key in done:continue
        start=time.time(); frac=Fraction(key)
        if deep and not any(r['counts'][-1] for r in prior[key]['checks'][-1]['checked']):
            result={**prior[key],'deep_check':'all sampled cylinders already extinct by depth 34'}
            with out.open('a') as f:f.write(json.dumps(result)+'\n')
            continue
        candidates=[r['lambda'] for r in reversed(entry['rows']) if r['low_growth']]
        if deep:candidates=[x for x in candidates if x<=prior[key]['last_low']]
        # Validate candidate low-growth points from highest downward.
        checks=[]
        for lam in candidates:
            r=evaluate(frac,lam);checks.append({'lambda':lam,**r})
            if r['low_growth']:break
        result={'n':key,'last_low':checks[-1]['lambda'] if checks and checks[-1]['low_growth'] else None,
                'checks':checks,'seconds':time.time()-start,'depth':52 if deep else 34,'precision_digits':50,'kmax':12}
        with out.open('a') as f:f.write(json.dumps(result)+'\n')
        print(key,result['last_low'],'candidates',len(checks),'seconds',round(result['seconds'],1),flush=True)
