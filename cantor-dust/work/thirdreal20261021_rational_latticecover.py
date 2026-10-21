from fractions import Fraction as F
import json,math
from pathlib import Path
bands=[(F(11,9),F(2027,1624)),(F(89,73),F(171,137)),(F(101,79),F(183,143)),(F(89,57),F(171,89)),(F(143,61),F(237,101)),(F(137,57),F(219,89))]
bands+= [(1/b,1/a) for a,b in bands]
ints=[0]
for _ in range(7):ints=sorted([3*p+d for p in ints for d in (0,2)])
ints=ints[1:]
for qmax in [8,26,80,242,728,2186]:
 rows=[]
 for P in ints:
  for Q in ints:
   if Q>qmax:break
   for a,b in bands:
    lo=a*F(P+1,Q);hi=b*F(P,Q+1)
    if lo<hi and hi>1 and lo<3:rows.append((lo,hi,P,Q,a,b))
 edge=F(1);chosen=[]
 while edge<=3:
  good=[r for r in rows if r[0]<edge<r[1]]
  if not good:break
  best=max(good,key=lambda r:r[1]);chosen.append(best);edge=best[1]
 print(qmax, float(edge), len(chosen))
 if edge>3:
  data=[{'lo':str(r[0]),'hi':str(r[1]),'P':r[2],'Q':r[3],'slope_lo':str(r[4]),'slope_hi':str(r[5])} for r in chosen]
  Path('work/thirdreal20261021_rational_latticecover.json').write_text(json.dumps(data,indent=2))
  print(data);break
