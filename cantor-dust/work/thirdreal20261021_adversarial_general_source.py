from pathlib import Path
from fractions import Fraction as F
from thirdreal20261021_adversarial_returns import check
import json

def root_bounds(value,power):
    scale=10**80;low=0;high=4*scale
    target=value.numerator*scale**power
    assert target<high**power*value.denominator
    while high-low>1:
        middle=(low+high)//2
        if middle**power*value.denominator<=target:low=middle
        else:high=middle
    return F(low,scale),F(high,scale)

def verify(a,b,j,P,p,Q,q,record):
    assert a>b
    for prefix,depth in ((P,p),(Q,q)):
        assert 0<prefix<3**depth
        for _ in range(depth):
            prefix,digit=divmod(prefix,3)
            assert digit in (0,2)
        assert prefix==0
    slope=F(record['lower']);assert slope==F(record['upper'])
    left=root_bounds(F(3)**(j+b*(q-p))*F(P,3**p)**(a-b),b)
    right=root_bounds(F(3)**(j+b*(q-p))*F(P+1,3**p)**(a-b),b)
    level_lo=(Q+1-F(b,a)*P*left[1])/2
    level_hi=(Q+1-F(b,a)*P*left[0])/2
    lipschitz=max(abs(left[0]-slope),abs(right[1]-slope))/2
    k=100
    while (a*k+j)%b:k+=1
    m=(a*k+j)//b
    factor=F(3,2) if a<2*b else F(1)
    constant_error=factor*F(a-b,4*b)*F(3)**(q-m)
    derivative_error=factor*F(a-b,2*b)*F(3)**(-m)
    permitted=F(record['margin'])/(2*3**record['depth'])
    assert lipschitz+derivative_error<permitted
    switches=[(F(1,3),(slope+1)/6),(slope/3,(slope+3)/6),((slope+1)/3,(3*slope+1)/6)]
    components=[i for i,(lo,hi) in enumerate(switches) if lo<level_lo-constant_error and level_hi+constant_error<hi]
    assert components
    returns=check(slope,record['depth'])
    assert returns['history']==[[h['depth'],h['one_intervals'],h['two_intervals'],h['covered_components']]for h in record['history']]
    return {'status':'PASS','a':a,'b':b,'P':P,'p':p,'Q':Q,'q':q,'slope':str(slope),'k':k,'m':m,'switch_components':components,'return_depth':returns['depth'],'actual_lipschitz_upper':str(lipschitz+derivative_error),'permitted_lipschitz':str(permitted),'dimension_lower_bound':f'log(2)/({returns["depth"]}*log(3))'}

if __name__=='__main__':
    rows=json.loads(Path('work/thirdreal20261021_parent_model.json').read_text())
    row=next(r for r in rows if r['a']==11 and r['b']==4 and r['return_certificate']['complete'])
    result=verify(row['a'],row['b'],row['j'],row['P'],row['depth'],row['Q'],row['depth'],row['return_certificate'])
    Path('work/thirdreal20261021_adversarial_114_verified.json').write_text(json.dumps(result,indent=2))
    print(result)
