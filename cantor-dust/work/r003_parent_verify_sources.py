from fractions import Fraction as F
from pathlib import Path
import json,sys
sys.set_int_max_str_digits(0)

bands=[(F(89,73),F(171,137)),(F(101,79),F(183,143)),
       (F(89,57),F(171,89)),(F(143,61),F(237,101)),(F(137,57),F(219,89))]
bands += [(1/b,1/a) for a,b in bands]

def prefix_ok(value,depth):
    assert 0<=value<3**depth
    for _ in range(depth):
        assert value%3 in (0,2)
        value//=3
    assert value==0

successful=set()
for filename in ('r003_construction_axis_2_100.json','r003_construction_axis_101_300.json'):
    rows=json.loads(Path('work',filename).read_text())
    for row in rows:
        if row.get('found') is False:continue
        n,d,p,q,P,Q=[row[key] for key in ('n','d','p','q','P','Q')]
        prefix_ok(P,p);prefix_ok(Q,q)
        assert P>0 and Q>0
        scale=F(3)**d
        assert scale*F(P,3**p)**n < n*F(Q+1,3**q)
        assert scale*F(P+1,3**p)**n > n*F(Q,3**q)
        lo=scale*F(3)**(q-p)*F(P,3**p)**(n-1)
        hi=scale*F(3)**(q-p)*F(P+1,3**p)**(n-1)
        assert [lo,hi]==list(map(F,row['ratio']))
        assert any(a<lo<hi<b for a,b in bands)
        successful.add(n)
print('Verified exact axis sources:',len(successful))
print('Missing axis-source exponents 2..300:', sorted(set(range(2,301))-successful))
for filename in ('r003_parent_elementary_sources.json','r003_parent_wide_sources.json'):
    for row in json.loads(Path('work',filename).read_text()):
        if row.get('found') is False:continue
        n,p,q,P,Q=[row[key] for key in ('n','p','q','P','Q')]
        prefix_ok(P,p);prefix_ok(Q,q)
        assert 0<P<P+1<3**p and 0<Q<Q+1<3**q
        assert F(P,3**p)**n+F(Q,3**q)**n<1
        assert F(P+1,3**p)**n+F(Q+1,3**q)**n>1
        lo=F(3)**(p-q)*F(Q*3**p,(P+1)*3**q)**(n-1)
        hi=F(3)**(p-q)*F((Q+1)*3**p,P*3**q)**(n-1)
        assert [lo,hi]==[F(row['normal_min']),F(row['normal_max'])]
        a,b=map(F,row['band'])
        assert a<lo<hi<b
        successful.add(n)
print('Including direct source certificates and previously proved n2:')
successful.add(2)
print('Uncertified by combined finite files through 300:',sorted(set(range(2,301))-successful))

# New proofs are bounded antichain-return certificates, independently rebuilt
# by r003_parent_antichain_verify.py, not applications of the five bands above.
new_returns=[]
for n in (9,10,23,25,28,31,32,78,82):
    verification=json.loads(Path(f'work/r003_parent_antichain_verify_n{n}.json').read_text())
    compact=json.loads(Path(f'work/r003_digits_compact_antichain_n{n}.json').read_text())
    assert verification['verification']=='PASS'
    assert verification['every_endpoint_matches']
    assert verification['source']==compact['source']
    assert verification['return_depth']==compact['depth']
    assert F(verification['amplified_lipschitz'])<F(verification['return_margin'])
    if n not in (9,10):
        assert verification['all_two_intervals_sha256_ascii_comma_newline']==compact['all_two_intervals_sha256_ascii_comma_newline']
    successful.add(n)
    new_returns.append({'n':n,'return_depth':compact['depth'],
                        'hausdorff_lower_bound':verification['hausdorff_lower_bound']})
assert set(range(2,301))<=successful
report={'verified_range':[2,300],'integer_count':299,
        'previous_method_count':290,'new_return_certificates':new_returns,
        'missing':[],'all_integer_goal_complete':False,
        'remaining_gap':'No usable explicit threshold for eventual all-n theorem; n>300 below that unknown threshold remains untreated.'}
Path('work/r003_parent_finite_coverage.json').write_text(json.dumps(report,indent=2))
print('All 299 integers 2..300 now covered; universal all-integer theorem remains open.')
