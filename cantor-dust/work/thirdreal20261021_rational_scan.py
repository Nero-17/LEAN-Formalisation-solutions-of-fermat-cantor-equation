from fractions import Fraction as F
from pathlib import Path
from bisect import bisect_right
from math import gcd,log,floor
import json,sys,time
import numpy as np
bands=[(F(11,9),F(2027,1624)),(F(89,73),F(171,137)),(F(101,79),F(183,143)),(F(89,57),F(171,89)),(F(143,61),F(237,101)),(F(137,57),F(219,89))]
bands += [(1/b,1/a) for a,b in bands]
def prefixes(depth):
 out=[0]
 for _ in range(depth):out=sorted(3*p+d for p in out for d in (0,2))
 return out[1:]
def rows(depth=7):
 out=[]
 ints=prefixes(depth)
 for P in ints:
  for Q in ints:
   for bi,(lo,hi) in enumerate(bands):
    left=lo*F(P+1,Q);right=hi*F(P,Q+1)
    if left<right and right>1 and left<3:out.append((left,right,P,Q,bi))
 return out
def merged(rows,B):
 arr=[]
 for lo,hi,P,Q,bi in rows:
  lo=max(lo,(F(11,10*B)-F(1,Q+1))*(P+1))
  if lo<hi and hi>1 and lo<3:arr.append((lo,hi))
 arr.sort();out=[]
 for lo,hi in arr:
  if out and lo<out[-1][1]:out[-1]=(out[-1][0],max(hi,out[-1][1]))
  else:out.append((lo,hi))
 return out

def exact(a,b,P,Q,J,bi):
 lo,hi=bands[bi]
 if not lo<F(a*Q,b*(P+1)) or not F(a*(Q+1),b*P)<hi:return False
 factor=b**b
 f3=3**abs(J)
 if J>=0:
  return f3*factor*P**a<a**b*(Q+1)**b and f3*factor*(P+1)**a>a**b*Q**b
 return factor*P**a<f3*a**b*(Q+1)**b and factor*(P+1)**a>f3*a**b*Q**b

def run(maxn=100,maxb=109):
 start=time.time();rr=rows();print('rows',len(rr),flush=True)
 ps=np.array([r[2] for r in rr]);qs=np.array([r[3] for r in rr]);bis=np.array([r[4] for r in rr]);ls=np.array([float(bands[r[4]][0]) for r in rr]);hs=np.array([float(bands[r[4]][1]) for r in rr])
 cert=[];missing=[];widthcount=0;total=0;phasecount=0
 for b in range(2,maxb+1):
  cover=merged(rr,b);starts=[r[0] for r in cover]
  for a in range(b+1,maxn*b):
   if gcd(a,b)!=1:continue
   total+=1;n=F(a,b);scale=1
   while n>=3*scale:scale*=3
   t=n/scale;idx=bisect_right(starts,t)-1
   if idx>=0 and cover[idx][0]<t<cover[idx][1]:widthcount+=1;continue
   P=ps*scale;nf=a/b
   valid=(ls<nf*qs/(P+1))&(nf*(qs+1)/P<hs)
   inds=np.flatnonzero(valid)
   low=(b*np.log(nf*qs[inds])-a*np.log(P[inds]+1))/log(3)
   high=(b*np.log(nf*(qs[inds]+1))-a*np.log(P[inds]))/log(3)
   js=np.floor(low).astype(np.int64)+1
   hits=np.flatnonzero(js<high-1e-10)
   found=None
   for h in hits:
    i=int(inds[h]);j=int(js[h]);p=int(P[i]);q=int(qs[i]);bi=int(bis[i])
    if exact(a,b,p,q,j,bi):found=[a,b,p,q,j,bi];break
   if found:cert.append(found);phasecount+=1
   else:missing.append([a,b])
  if b%10==0 or b==maxb:print(b,'total',total,'width',widthcount,'phase',phasecount,'missing',len(missing),'seconds',round(time.time()-start,1),flush=True)
 out={'range':[1,maxn],'max_denominator':maxb,'prefix_depth':7,'total':total,'lattice_width_covered':widthcount,'individual_sources':cert,'missing':missing,'seconds':time.time()-start}
 path=Path(f'work/thirdreal20261021_rational_scan_{maxn}.json');path.write_text(json.dumps(out,separators=(',',':')))
 print('DONE',path,len(missing),missing[:100],flush=True)
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 100)
