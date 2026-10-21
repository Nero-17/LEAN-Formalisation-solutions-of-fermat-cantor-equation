"""Exact finite-core and periodic-point uniqueness certificate for n=5."""
from fractions import Fraction as F
from pathlib import Path
import json,time
wx='101000100000';wv='110000010010'
def endpoint(w,l):return (1-l)*sum((l**i for i,b in enumerate(w) if b=='1'),F(0))
def periodic(l):
    u=endpoint(wx,l)+l**len(wx)/(1+l)
    v=endpoint(wv,l)+l**len(wv)/(1+l)
    return u**5+(1-l*l*v)**5-1
lo=F('0.26999925');hi=F('0.26999926')
assert periodic(lo)>0>periodic(hi)
for _ in range(110):
    m=(lo+hi)/2
    if periodic(m)>0:lo=m
    else:hi=m
assert periodic(lo)>0>periodic(hi)
def value(w,v,l,upper):
    u=endpoint(w,l)+(l**len(w) if upper else 0)
    vv=endpoint(v,l)+(0 if upper else l**len(v))
    return u**5+(1-l*l*vv)**5-1
stack=[('1','1')];leaves=[];target=[];unresolved=[];start=time.time()
while stack:
    w,v=stack.pop()
    if (w,v)==(wx,wv):target.append((w,v));continue
    low=value(w,v,hi,False);high=value(w,v,lo,True)
    if low>0 or high<0:
        leaves.append({'xword':w,'vword':v,'sign':'+' if low>0 else '-','margin':str(low if low>0 else -high)});continue
    if len(w)>=24:unresolved.append((w,v));continue
    for a in '01':
        for b in '01':stack.append((w+a,v+b))
assert target==[(wx,wv)] and not unresolved
paths=[tuple(zip(z['xword'][1:],z['vword'][1:])) for z in leaves]+[tuple(zip(wx[1:],wv[1:]))]
assert len(set(paths))==len(paths)
assert sum((F(1,4**len(p)) for p in paths),F(0))==1
assert not any(p!=q and len(p)<=len(q) and q[:len(p)]==p for p in paths for q in paths)
# Coordinate endpoint monotonicity gives uniform bounds throughout the root bracket.
u_min=endpoint(wx,hi);u_max=endpoint(wx,lo)+lo**len(wx)
v_min=endpoint(wv,hi);v_max=endpoint(wv,lo)+lo**len(wv)
y_min=1-hi**2*v_max;y_max=1-lo**2*v_min
b_min=1-hi-hi**2
slope_min=lo**2*(y_min/u_max)**4
slope_max=hi**2*(y_max/u_min)**4
lower_gap=slope_min-hi**2/b_min
upper_gap=b_min-slope_max
assert lower_gap>0 and upper_gap>0
out={'status':'PASS','exponent':5,'lambda_root_interval':[str(lo),str(hi)],'lambda_decimal':str(float((lo+hi)/2)),'periodic_root_signs':[str(periodic(lo)),str(periodic(hi))],'target_words':[wx,wv],'target_tail':'(10)^infinity, actual tail 1/(1+lambda)','excluded':leaves,'remaining_target':target,'unresolved':unresolved,'kraft':'1','slope_bounds':list(map(str,[slope_min,slope_max])),'periodic_uniqueness_margins':list(map(str,[lower_gap,upper_gap])),'scope':'At the unique periodic parameter root, the entire core has precisely one point. Together with the global window reduction, E has exactly four points.','seconds':time.time()-start}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2))
print('PASS',float(lo),len(leaves),'leaves','slope',float(slope_min),float(slope_max),'gaps',float(lower_gap),float(upper_gap),'seconds',time.time()-start)
