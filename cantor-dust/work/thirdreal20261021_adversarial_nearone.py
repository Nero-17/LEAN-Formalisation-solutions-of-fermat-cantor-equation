from pathlib import Path
from fractions import Fraction as F
from thirdreal20261021_adversarial_returns import check
import json

def root_bounds(numerator,denominator,power):
    scale=10**80;low=scale;high=2*scale
    target=numerator*scale**power
    assert low**power*denominator<target<high**power*denominator
    while high-low>1:
        middle=(low+high)//2
        if middle**power*denominator<=target:low=middle
        else:high=middle
    return F(low,scale),F(high,scale)

records=json.loads(Path('work/thirdreal20261021_irrational_nearone_returns.json').read_text())
results=[]
for record in records:
    if not record['complete']:continue
    source=record['source'];a,b,j=source['a'],source['b'],source['j']
    assert a==b+1
    P,Q,depth=source['P'],source['Q'],source['depth']
    for prefix in (P,Q):
        assert 0<prefix<3**depth
        for _ in range(depth):
            prefix,digit=divmod(prefix,3)
            assert digit in (0,2)
        assert prefix==0
    slope=F(record['lower']);assert slope==F(record['upper'])
    left=root_bounds(3**j*P,3**depth,b)
    right=root_bounds(3**j*(P+1),3**depth,b)
    level_lo=(Q+1-F(b,a)*P*left[1])/2
    level_hi=(Q+1-F(b,a)*P*left[0])/2
    lipschitz=max(abs(left[0]-slope),abs(right[1]-slope))/2
    k=100
    while (a*k+j)%b:k+=1
    m=(a*k+j)//b
    constant_error=F(3,8*b*3**(m-depth))
    derivative_error=F(3,4*b*3**m)
    permitted=F(record['margin'])/(2*3**record['depth'])
    assert lipschitz+derivative_error<permitted
    switches=[(F(1,3),(slope+1)/6),(slope/3,(slope+3)/6),((slope+1)/3,(3*slope+1)/6)]
    components=[i for i,(lo,hi) in enumerate(switches) if lo<level_lo-constant_error and level_hi+constant_error<hi]
    assert components
    returns=check(slope,record['depth'])
    assert returns['history']==[[h['depth'],h['one_intervals'],h['two_intervals'],h['covered_components']]for h in record['history']]
    results.append({'status':'PASS','a':a,'b':b,'P':P,'Q':Q,'source_depth':depth,'slope':str(slope),'k':k,'m':m,'switch_components':components,'return_depth':returns['depth'],'actual_lipschitz_upper':str(lipschitz+derivative_error),'permitted_lipschitz':str(permitted),'dimension_lower_bound':f'log(2)/({returns["depth"]}*log(3))'})
    print(a,b,'INDEPENDENT PASS',returns['depth'],flush=True)
    Path('work/thirdreal20261021_adversarial_nearone_verified.json').write_text(json.dumps(results,indent=2))
