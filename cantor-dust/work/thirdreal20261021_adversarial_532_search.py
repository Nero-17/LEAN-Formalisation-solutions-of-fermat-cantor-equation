from pathlib import Path
from decimal import Decimal as D,getcontext
from fractions import Fraction as F
import json,math,sys
getcontext().prec=85

def prefixes(depth):
    result=[0]
    for _ in range(depth):result=[3*p+d for p in result for d in (0,2)]
    return result

output=[]
for h in (2,3):
  initial=[(P,2) for P in prefixes(1+h) if P>=2*3**h]
  for j in range(1,41):
    nodes=initial
    for q in range(1,46):
      p=q+h
      exponent=53*p-2*q-j
      factor=2809*3**exponent
      def crosses(P,Q):
        return 4*P**53<factor*(Q+1)**2 and 4*(P+1)**53>factor*Q**2
      nodes=[(P,Q)for P,Q in nodes if crosses(P,Q)]
      if not nodes:break
      next_factor=factor*3**51
      def children(P,Q):
        result=[]
        for x in (0,2):
          pp=3*P+x;left=4*pp**53;right=4*(pp+1)**53
          for y in (0,2):
            qq=3*Q+y
            if left<next_factor*(qq+1)**2 and right>next_factor*qq**2:result.append((pp,qq))
        return result
      following=[]
      for P,Q in nodes:
        cc=children(P,Q)
        if q>=40 and len(cc)>=2:
          u=D(P)/D(3)**p
          r=D(3)**(D(j)/2-h)*u**(D(51)/2)
          level=(D(Q+1)-D(2)/53*r*P)/2
          if D(1)<r<D(3):
            output.append({'a':53,'b':2,'j':j,'P':P,'p':p,'Q':Q,'q':q,'r':str(r),'level':str(level),'swap':False})
          elif D(1)/3<r<D(1):
            output.append({'a':53,'b':2,'j':j,'P':P,'p':p,'Q':Q,'q':q,'r':str(1/r),'level':str(level/r),'swap':True})
        following.extend(cc)
      nodes=following
      if len(nodes)>150:nodes=[nodes[round(i*(len(nodes)-1)/149)]for i in range(150)]
      if q>=40:break
    if output:
      Path('work/thirdreal20261021_adversarial_532_candidates.json').write_text(json.dumps(output,indent=2))
    print('phase',h,j,'candidates',len(output),flush=True)
print('DONE',len(output),flush=True)
