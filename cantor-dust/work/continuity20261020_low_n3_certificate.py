from fractions import Fraction as F
import json
from pathlib import Path
l=F(38,125)
def endpoints(word):
    left=(1-l)*sum((int(bit)*l**j for j,bit in enumerate(word)),F(0))
    return left,left+l**len(word)
leaves=[('10','10','-'),('10','11','-'),('11','10','+'),('110','110','-'),('110','111','-'),('111','110','+'),('111','111','+')]
checks={
 'both_lower':1-2*l**3,
 'phase_nonpositive':3*(1-l)**3-1,
 'phase_ge2':(1-l)**3-3*l*l,
 'upper_10_10':1-2*(1-l+l*l)**3,
 'upper_cross':(1-l)**3+(1-l*l)**3-1,
}
rows=[]
for wx,wy,sign in leaves:
 x0,x1=endpoints(wx);y0,y1=endpoints(wy)
 positive=x0**3-3*l*y1
 negative=-(x1**3-l*y0*(3-3*l**4*y0+l**8*y0*y0))
 margin=positive if sign=='+' else negative
 assert margin>0,(wx,wy,margin)
 rows.append({'x_word':wx,'y_word':wy,'sign':sign,'margin_exact':str(margin),'margin_float':float(margin)})
 assert len(wx)==len(wy)
assert sum((F(1,4**(len(wx)-1)) for wx,wy,_ in leaves),F(0))==1
for i,(wx,wy,_) in enumerate(leaves):
 for vx,vy,_ in leaves[i+1:]:
  assert not ((vx.startswith(wx) and vy.startswith(wy)) or (wx.startswith(vx) and wy.startswith(vy)))
assert all(value>0 for value in checks.values())
result={'lambda':str(l),'geometric_margins':{key:{'exact':str(val),'decimal':float(val)} for key,val in checks.items()},'leaves':rows,'kraft_sum':'1','prefix_free':True,'pass':True}
Path('work/continuity20261020_low_n3_certificate.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result,indent=2))
