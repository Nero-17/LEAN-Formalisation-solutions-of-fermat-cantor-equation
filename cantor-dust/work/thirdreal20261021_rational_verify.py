from fractions import Fraction as F
from pathlib import Path
import json
p=Path('work/thirdreal20261021_rational_latticecover_optimized.json')
data=json.loads(p.read_text());B=data['denominator'];edge=F(1)
bands=[(F(11,9),F(2027,1624)),(F(89,73),F(171,137)),(F(101,79),F(183,143)),(F(89,57),F(171,89)),(F(143,61),F(237,101)),(F(137,57),F(219,89))]
bands += [(1/b,1/a) for a,b in bands]
def legal(x):
 while x:
  x,d=divmod(x,3)
  if d not in (0,2):return False
 return True
for row in data['rows']:
 P,Q=row['P'],row['Q'];a,b=F(row['slope_lo']),F(row['slope_hi'])
 lo,hi=F(row['lo']),F(row['hi'])
 assert legal(P) and legal(Q) and (a,b) in bands
 assert lo>=a*F(P+1,Q) and hi<=b*F(P,Q+1)
 assert lo>=(F(11,10*B)-F(1,Q+1))*(P+1)
 assert lo<edge<hi
 edge=hi
assert edge>3
# e^(11/10)>3 by a finite positive series
assert sum((F(11,10)**j)/__import__('math').factorial(j) for j in range(6))>3
out={'status':'PASS','denominator_cutoff':B,'rows':len(data['rows']),'covered_interval':['1','3'],'bounds':'All exact Fraction inequalities; ln3<11/10 and ln(1+u)>u/(1+u).'}
Path('work/thirdreal20261021_rational_lattice_verified.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
