from pathlib import Path
from fractions import Fraction as F
import hashlib,json

root=Path('work')
def legal(prefix,depth):
    if not 0<prefix<3**depth:return False
    while prefix:
        prefix,digit=divmod(prefix,3)
        if digit not in (0,2):return False
    return True

audited=[]
for m in (12,13,14):
    domains=[]
    for half in ('lower','upper'):
        stem=f'alln20261020_fixed_m{m}_{half}'
        candidate=root/(stem+'_candidate.json')
        verified=json.loads((root/(stem+'_verified.json')).read_text())
        data=json.loads(candidate.read_text())
        assert verified['verification']=='PASS'
        assert hashlib.sha256(candidate.read_bytes()).hexdigest()==verified['input_sha256']
        domain=tuple(map(F,verified['parameter_domain']))
        assert domain==tuple(map(F,data['parameter_domain']))
        assert verified['parameter_cells']==len(data['cells'])
        intervals=[]
        for row in data['cells']:
            depth=row.get('endpoint_depth',data['endpoint_depth'])
            height=row.get('height',data['height'])
            assert m>=depth+height
            assert legal(row['P'],depth)
            lower,upper=F(*row['t_lower']),F(*row['t_upper'])
            assert domain[0]<=lower<upper<=domain[1]
            intervals.append((lower,upper))
        edge=domain[0]
        for lower,upper in sorted(intervals):
            assert lower<=edge
            edge=max(edge,upper)
        assert edge==domain[1]
        domains.append(domain)
        audited.append({'file':stem,'cells':len(intervals),'hash_match':True})
    assert domains==[(F(1),F(2)),(F(2),F(3))]

candidate=root/'alln20261020_finite_z_m15_h3_depth11.json'
data=json.loads(candidate.read_text())
hash_value=hashlib.sha256(candidate.read_bytes()).hexdigest()
for name,status_key in [('alln20261020_finite_z_m15_depth11_verified.json','verification'),('alln20261020_parent_finite_m15_verified.json','status')]:
    verified=json.loads((root/name).read_text())
    assert verified[status_key]=='PASS'
    assert verified['input_sha256']==hash_value
    assert verified['minimum_m']==15 and verified['minimum_z']==20*3**10
assert 15>=11+3
intervals=[]
for row in data['t_cover']:
    prefix,start,end=row[2:]
    assert legal(prefix,11) and F(prefix,3**11)>=F(20,243)
    intervals.append((F((2*start-1)*prefix,4000*3**11),F((2*end+1)*prefix,4000*3**11)))
edge=F(1)
for lower,upper in sorted(intervals):
    assert lower<=edge
    edge=max(edge,upper)
assert edge>=3
result={'status':'PASS','scope':'Retained report hashes, legal geometry, exact parameter-domain joins; earlier full interval calculations not rerun','fixed_scales':audited,'tail_endpoint_intervals':len(intervals),'minimum_exponent':3**12}
(root/'thirdreal20261021_adversarial_large_verified.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
