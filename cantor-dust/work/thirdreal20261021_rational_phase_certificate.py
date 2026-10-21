from fractions import Fraction as F
from functools import lru_cache
from bisect import bisect_left,bisect_right
from pathlib import Path
import math,json,time,sys
from alln20261020_verify_fixed_m import prefixes,BANDS
from thirdreal20261021_rational_logbounds import logint,S as LOG_SCALE
S=1<<80

def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)
@lru_cache(None)
def log3units(x):
 a,b=logint(x.numerator);c,d=logint(x.denominator);e,f=logint(3)
 vals=[F(S*z,w)for z in (a-d,b-c)for w in (e,f)]
 return floor(min(vals)),ceil(max(vals))
@lru_cache(None)
def rational3units(x):
 a,b=logint(3);vals=[F(S*LOG_SCALE*x,w)for w in(a,b)]
 return floor(min(vals)),ceil(max(vals))

def modular_cover(intervals,total,b):
 out=[]
 for lo,hi in intervals:
  lo*=b;hi*=b
  if hi-lo>=total:return True
  shift=lo//total;lo-=shift*total;hi-=shift*total
  out.append((lo,min(hi,total)))
  if hi>total:out.append((0,hi-total))
 end=0
 for lo,hi in sorted(out):
  if lo>end:return False
  end=max(end,hi)
 return end>=total

class Verifier:
 def __init__(self,m,D,h,depth=4,uniform=False):
  self.m=m;self.M=3**m;self.D=D;self.h=h;self.depth=depth;self.uniform=uniform
  assert m>=D+h
  self.qs=[2*3**depth+b for b in prefixes(depth)]
  self.logs={q:log3units(F(q,3**(depth+1)))for q0 in self.qs for q in(q0,q0+1)}
  self.ps=range(max(0,depth+h-2),depth+h+4);self.geometries={}
 def build(self,P):
  assert P>0 and P in prefixes(self.D)
  Mu=self.M*P//3**self.D;center=F(3**self.h,2);hh={};rows={}
  for p in self.ps:
   length=3**(p-self.h)
   for A in prefixes(p):
    for value in(A,A+1):
     a=F(value,length)
     if a in hh:continue
     lo,hi=log3units((Mu+center)/(Mu+a));lo*=self.M;hi*=self.M
     if self.uniform:
      l,h=rational3units((center-a)*F(3**self.D,P));lo=min(lo,l);hi=max(hi,h)
     hh[a]=(lo,hi)
   rows[p]=[(A,hh[F(A+1,length)][1],hh[F(A,length)][0])for A in prefixes(p)]
  self.geometries[P]=(Mu,rows)
 def intervals(self,P,tlo,thi):
  if P not in self.geometries:self.build(P)
  Mu,rows=self.geometries[P];den=math.lcm(tlo.denominator,thi.denominator);low=tlo.numerator*(den//tlo.denominator);high=thi.numerator*(den//thi.denominator);total=den*S;inset=ceil(F(total,10**12));out=[]
  for p in self.ps:
   length=3**(p-self.h)
   for q in self.qs:
    ranges=[]
    for blo,bhi in BANDS:
     amax=(low*q*self.M*blo.denominator-1)//(den*blo.numerator)-Mu*length-1
     if self.uniform:
      if high*(q+1)*3**self.D*bhi.denominator>=den*bhi.numerator*P*length:continue
      amin=0
     else:amin=high*(q+1)*self.M*bhi.denominator//(den*bhi.numerator)-Mu*length+1
     i=bisect_left(prefixes(p),amin);j=bisect_right(prefixes(p),amax)
     if i<j:ranges.append((i,j))
    merged=[]
    for i,j in sorted(ranges):
     if merged and i<=merged[-1][1]:merged[-1][1]=max(merged[-1][1],j)
     else:merged.append([i,j])
    for i,j in merged:
     for _,hl,hu in rows[p][i:j]:
      lo=self.logs[q][1]*den+(high if hl>=0 else low)*hl+inset
      hi=self.logs[q+1][0]*den+(low if hu>=0 else high)*hu-inset
      if lo<hi:out.append((lo,hi))
  return out,total
 def covers(self,P,tlo,thi):
  intervals,total=self.intervals(P,tlo,thi)
  return all(modular_cover(intervals,total,b)for b in range(2,110))

def discover(m,D,h,uniform=False,step=200):
 from thirdreal20261021_rational_uniform_probe import intervals as uniform_intervals
 from thirdreal20261021_rational_finite_probe import finite_intervals
 from alln20261020_inner_phase_probe import modular_gaps
 import numpy as np
 float_intervals=uniform_intervals if uniform else finite_intervals
 endpoints=[p for p in prefixes(D)if p>0];recent=endpoints.copy();v=Verifier(m,D,h,uniform=uniform);stack=[(F(i,step),F(i+1,step),0)for i in range(3*step-1,step-1,-1)];cells=[];fail=[];start=time.time()
 while stack:
  lo,hi,level=stack.pop();found=None
  for P in recent:
   ll,uu=float_intervals(float(lo),float(hi),m,P,D,h)
   if all(not modular_gaps(b*ll,b*uu)for b in range(2,110)) and v.covers(P,lo,hi):found=P;break
  if found:
   cells.append([str(lo),str(hi),found]);recent.remove(found);recent.insert(0,found)
  elif level<12:
   mid=(lo+hi)/2;stack.extend([(mid,hi,level+1),(lo,mid,level+1)])
  else:fail.append([str(lo),str(hi)])
  if len(cells)%100==0 and found:print('progress',m,uniform,len(cells),len(stack),len(fail),round(time.time()-start,1),flush=True)
  if len(fail)>20:break
 out={'status':'PASS'if not fail and not stack else'INCOMPLETE','m':m,'endpoint_depth':D,'height':h,'uniform_tail':uniform,'denominators':[2,109],'cells':cells,'failures':fail,'remaining':len(stack),'seconds':time.time()-start}
 tag=f'tail_m{m}'if uniform else f'fixed_m{m}';Path(f'work/thirdreal20261021_rational_{tag}.json').write_text(json.dumps(out,separators=(',',':')))
 print('DONE',tag,out['status'],len(cells),fail[:20],round(time.time()-start,1),flush=True)
 return out
if __name__=='__main__':
 mode=sys.argv[1]if len(sys.argv)>1 else'tail'
 if mode=='tail':discover(9,6,1,True)
 else:
  m=int(mode);discover(m,m-1,1)
