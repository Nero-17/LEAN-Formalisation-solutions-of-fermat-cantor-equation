"""Independent reconstruction of fixed-scale modular phase coverage.
Uses the reviewer's independently developed Horner logarithm bounds,
not the producer's successive-power logarithms or interval implementation.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
from bisect import bisect_left,bisect_right
import json,sys,math,time,hashlib
S=1<<200;U=1<<80
def ceildiv(a,b):return -((-a)//b)
def unit(x,y):
 assert 0<=3*x<=y
 lo=S*x//y;hi=ceildiv(S*x,y);llo=lo*lo//S;hhi=ceildiv(hi*hi,S);a=b=0
 for k in range(69,-1,-1):
  a=S//(2*k+1)+llo*a//S;b=ceildiv(S,2*k+1)+ceildiv(hhi*b,S)
 return 2*(lo*a//S),2*ceildiv(hi*b,S)+ceildiv(3*S,141*3**141)
L2=unit(1,3)
@lru_cache(None)
def ilog(v):
 e=v.bit_length()-1;p=1<<e;a,b=unit(v-p,v+p)
 return e*L2[0]+a,e*L2[1]+b
@lru_cache(None)
def lg(x):
 a,b=ilog(x.numerator);c,d=ilog(x.denominator);l,h=ilog(3)
 vv=[F(U*z,q) for z in (a-d,b-c) for q in (l,h)]
 low=min(vv);high=max(vv)
 return low.numerator//low.denominator,ceildiv(high.numerator,high.denominator)
@lru_cache(None)
def digits(depth):
 out=[0]
 for _ in range(depth):out=[3*x+y for x in out for y in (0,2)]
 return out
bands=[(F(11,9),F(2027,1624)),(F(11,7),F(21,11)),(F(89,73),F(171,137)),(F(101,79),F(183,143)),(F(89,57),F(171,89)),(F(143,61),F(237,101)),(F(137,57),F(219,89))]
bands +=[(1/b,1/a) for a,b in bands.copy()]
def covers(intervals,total,b):
 pieces=[]
 for left,right in intervals:
  left*=b;right*=b
  if right-left>=total:return True
  shift=left//total;left-=shift*total;right-=shift*total
  if right>total:pieces.extend([(left,total),(0,right-total)])
  else:pieces.append((left,right))
 edge=0
 for left,right in sorted(pieces):
  if left>edge:return False
  edge=max(edge,right)
 return edge==total
def verify(m):
 path=Path(f'work/thirdreal20261021_rational_grouped_fixed_m{m}.json');data=json.loads(path.read_text());assert data['status']=='PASS' and not data['uniform']
 D=data['D'];h=data['h'];assert m>=D+h;M=3**m;geom={};qs=[2*3**4+q for q in digits(4)];ps=range(4+h-2,4+h+4)
 qlogs={q:lg(F(q,3**5)) for z in qs for q in (z,z+1)}
 def geometry(P):
  assert P in digits(D) and P>0
  center=F(3**h,2);Mu=F(M*P,3**D);assert Mu.denominator==1;Mu=int(Mu);rows={}
  for p in ps:
   length=3**(p-h);lst=[]
   for A in digits(p):
    low=lg((Mu+center)/(Mu+F(A+1,length)))[1]*M
    high=lg((Mu+center)/(Mu+F(A,length)))[0]*M
    lst.append((A,low,high))
   rows[p]=lst
  return Mu,rows
 start=time.time();edge=F(1);groups_checked=0;denomchecks=0
 for index,(aa,bb,groups) in enumerate(data['cells']):
  a,b=F(aa),F(bb);assert a==edge and a<b<=3;edge=b;seen=[]
  den=math.lcm(a.denominator,b.denominator);al=int(a*den);bh=int(b*den);total=den*U;inset=ceildiv(total,10**12)
  for P,denominators in groups:
   assert not set(denominators)&set(seen);seen+=denominators
   if P not in geom:geom[P]=geometry(P)
   Mu,rows=geom[P];intervals=[]
   for p in ps:
    length=3**(p-h)
    for q in qs:
     valid=set()
     for l,r in bands:
      lower=bh*(q+1)*M*r.denominator//(den*r.numerator)-Mu*length+1
      upper=(al*q*M*l.denominator-1)//(den*l.numerator)-Mu*length-1
      valid.update(range(bisect_left(digits(p),lower),bisect_right(digits(p),upper)))
     for i in valid:
      A,low,high=rows[p][i]
      # Direct derivative check independently confirms integer selection.
      rl=F(al*q*M,den*(Mu*length+A+1));rh=F(bh*(q+1)*M,den*(Mu*length+A))
      assert any(l<rl and rh<r for l,r in bands)
      left=qlogs[q][1]*den+max(al*low,bh*low)+inset
      right=qlogs[q+1][0]*den+min(al*high,bh*high)-inset
      if left<right:intervals.append((left,right))
   assert all(2<=d<=109 and covers(intervals,total,d) for d in denominators),(index,P,denominators)
   groups_checked+=1;denomchecks+=len(denominators)
  assert sorted(seen)==list(range(2,110))
  if (index+1)%100==0:print('m',m,'cells',index+1,'seconds',round(time.time()-start,1),flush=True)
 assert edge==3
 result=dict(status='PASS',m=m,cells=len(data['cells']),groups=groups_checked,denominator_checks=denomchecks,input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),seconds=time.time()-start,scope='Independent logarithms, reconstructed inner phase intervals, strict derivative bands, exact modular covers and full closed-parameter joins')
 Path(f'work/thirdreal20261021_parent_layer_m{m}_verified.json').write_text(json.dumps(result,indent=2));print(result,flush=True)
for m in map(int,sys.argv[1:]):verify(m)
