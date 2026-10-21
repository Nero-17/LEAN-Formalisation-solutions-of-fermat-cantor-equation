from decimal import Decimal as D,getcontext
from fractions import Fraction as F
from pathlib import Path
import json,time
from thirdreal20261021_irrational_scalar_bounded import check
getcontext().prec=95;n=D(8)/3
def pw(x):return x**n if x else D(0)
def geom(P,p,Q,q):
 x=D(P)/D(3)**p;y=D(Q)/D(3)**q;hx=D(3)**(-p);hy=D(3)**(-q)
 return x,y,hx,hy
def cross(P,p,Q,q):
 x,y,hx,hy=geom(P,p,Q,q)
 return pw(x)+pw(y)<1<pw(x+hx)+pw(y+hy)
nodes=[(0,0,0,0)];out=[]
for step in range(90):
 nxt=[]
 for P,p,Q,q in nodes:
  x,y,hx,hy=geom(P,p,Q,q)
  dx=n*(x+hx/2)**(n-1)*hx;dy=n*(y+hy/2)**(n-1)*hy
  cc=[(3*P+d,p+1,Q,q)for d in(0,2)] if dx>=dy else [(P,p,3*Q+d,q+1)for d in(0,2)]
  nxt.extend(c for c in cc if cross(*c))
  if min(p,q)>=35 and P and Q:
   dx=n*x**(n-1)*hx;dy=n*y**(n-1)*hy
   if dx<dy:P,p,Q,q=Q,q,P,p;x,y,hx,hy=y,x,hy,hx;dx,dy=dy,dx
   r=dx/dy;level=(1-pw(x)-pw(y))/(2*dy)
   if 1<r<3:
    bands=[(D(1)/3,(r+1)/6),(r/3,(r+3)/6),((r+1)/3,(3*r+1)/6)]
    if any(l+D('1e-6')<level<h-D('1e-6') for l,h in bands):
     out.append(dict(P=P,p=p,Q=Q,q=q,r=str(r),level=str(level)))
 nodes=nxt
 if len(nodes)>100:nodes=[nodes[round(i*(len(nodes)-1)/99)]for i in range(100)]
 if len(out)>=60:break
 print('tree',step,len(nodes),len(out),flush=True) if step%10==0 else None
Path('work/thirdreal20261021_parent_actual83_sources.json').write_text(json.dumps(out,indent=2));print('candidatecount',len(out),flush=True)
seen=set();results=[]
for row in out:
 r=F(row['r']).limit_denominator(10**25);key=round(float(r),4)
 if key in seen:continue
 seen.add(key);start=time.time();cert=check(r,20,1200000,margin=F(1,10**7))
 result={'source':row,'rational_slope':str(r),'certificate':cert};results.append(result)
 print('actual83',float(r),row['level'][:16],cert['complete'],cert['depth'],time.time()-start,flush=True)
 Path('work/thirdreal20261021_parent_actual83_returns.json').write_text(json.dumps(results,indent=2))
 if cert['complete']:break
