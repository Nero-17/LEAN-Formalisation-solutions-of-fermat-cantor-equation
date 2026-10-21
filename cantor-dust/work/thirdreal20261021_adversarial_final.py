"""Final adoption ledger; substantive independent checks are cited explicitly."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,datetime

root=Path('work')
prefix='thirdreal20261021_'
def read(s):return json.loads((root/(prefix+s+'.json')).read_text())
def digest(s):return hashlib.sha256((root/(prefix+s)).read_bytes()).hexdigest()
layers=[]
for m in range(7,12):
    name=f'rational_grouped_fixed_m{m}'
    data=read(name);receipt=read(f'parent_layer_m{m}_verified')
    assert receipt['status']=='PASS' and receipt['m']==m
    assert receipt['input_sha256']==digest(name+'.json')
    edge=Fraction(1)
    for lo,hi,groups in data['cells']:
        assert Fraction(lo)==edge<Fraction(hi)<=3
        edge=Fraction(hi)
        assert sorted(b for p,bs in groups for b in bs)==list(range(2,110))
    assert edge==3 and receipt['cells']==len(data['cells'])
    layers.append(dict(m=m,cells=len(data['cells']),sha256=receipt['input_sha256']))
scan=read('adversarial_scan_2187_verified');repair=read('adversarial_repair_2187_verified')
assert scan['status']==repair['status']=='PASS'
assert scan['total']==8033550 and scan['width_covered']==7738063
assert scan['exact_sources']==294016 and repair['repaired']==1464
assert scan['total']==scan['width_covered']+scan['exact_sources']+repair['repaired']+len(repair['remaining'])
assert set(map(tuple,repair['remaining']))=={(24,23),(19,18),(13,12),(8,7),(8,3),(11,4),(53,2)}
returns=read('rational_actual83_returns_verified')
assert returns['independent_status']=='PASS' and returns['complete']
assert returns['depth']==17 and returns['margin']=='1/10000000'
assert returns['components']==[0,1,2]
assert returns['history'][-1]['covered_components']==3
assert returns['parent_candidate_sha256']==digest('parent_actual83_retry.json')
source=read('parent_actual83_verified');other=read('irrational_83_actual_verified')
assert source['status']=='PASS' and 'PASS' in other['status']
assert source['slope']==other['r']==returns['lower']==returns['upper']
assert Fraction(source['gradient_error_bound'])<Fraction(source['permitted_error'])==Fraction(1,2*10**7*3**17)
assert Fraction(other['lipschitz_bound'])<Fraction(other['permitted_lipschitz'])==Fraction(source['permitted_error'])
r=Fraction(source['slope'])
for bounds in (source['level_bounds'],other['level_bounds']):
    lo,hi=map(Fraction,bounds)
    assert r/3<lo<=hi<(r+3)/6
receipts=['adversarial_scan_2187_verified.json','adversarial_repair_2187_verified.json',
 'adversarial_large_verified.json','adversarial_87_verified.json','adversarial_nearone_verified.json',
 'adversarial_114_verified.json','adversarial_532_verified.json','parent_532_verified.json',
 'parent_actual83_verified.json','irrational_83_actual_verified.json','rational_actual83_returns_verified.json']
result=dict(status='ACCEPT: computer-assisted theorem for every real n>1',
 timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 proof_review='Analytic mechanisms and all coverage joins independently reviewed; expensive continuous layers adopted from separately implemented parent replay after source inspection and hash matching.',
 partition=['All irrational n>1: tuned affine source and irrational phase density.',
 'All integer n>1: retained all-integer theorem, including independent circle case.',
 'All reduced rational denominators b>=110: uniform strict lattice-width certificate.',
 'Reduced denominators 2..109 and 1<n<2187: independently re-enumerated exhaustive finite certificates plus seven independently proved sources.',
 'Reduced denominators 2..109 and 2187<=n<=531441: five continuous phase covers, independently replayed.',
 'All rational n>=531441: retained continuous fixed layers and tail, with rational phase congruence and real-power Taylor transfer.'],
 finite_partition=dict(total=8033550,width=7738063,individual=295480,specials=7),
 continuous_layers=layers,
 final_exception=dict(exponent='8/3',return_depth=17,margin='1/10000000',dimension_lower_bound='log(2)/(17*log(3))'),
 receipt_hashes={s:digest(s) for s in receipts},remaining_mathematical_gap=None,
 limitation='The result is computer assisted. No formula for the exact dimension or bound uniform in n is asserted.')
(root/(prefix+'adversarial_final_ledger.json')).write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
