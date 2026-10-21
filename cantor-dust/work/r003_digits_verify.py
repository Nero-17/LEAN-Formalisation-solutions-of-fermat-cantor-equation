"""Independent checker: no SCC discovery, no floating arithmetic.
Checks all 1024 words against exact affine inequalities; graph ranks certify
that recurrent motion consists only of explicitly listed directed cycles.
"""
import json,itertools
from fractions import Fraction as Q

def feasible(word):
    lower=[];upper=[]
    digits=[(0,0),(0,1),(1,0),(1,1)]
    lows=[(0,0),(1,1),(1,3),(3,1)] # denominator 6
    highs=[(0,2),(2,0),(2,2),(3,3)]
    # T0's interval constraint at position j is prefix+j tail / 3^j.
    prefix_a=prefix_b=0
    for j,d in enumerate(word):
        den=6*3**j
        lower.append((Q(6*prefix_a+lows[d][0],den),Q(6*prefix_b+lows[d][1],den)))
        upper.append((Q(6*prefix_a+highs[d][0],den),Q(6*prefix_b+highs[d][1],den)))
        prefix_a=3*prefix_a+digits[d][0];prefix_b=3*prefix_b+digits[d][1]
    lo,hi=Q(1),Q(3)
    for a,b in lower:
        for c,d in upper:
            slope=a-c;intercept=b-d
            if not slope:
                if intercept>0:return None
            elif slope>0:hi=min(hi,-intercept/slope)
            else:lo=max(lo,-intercept/slope)
    return (lo,hi) if lo<=hi else None

cert=json.load(open('work/r003_digits_graph_certificate.json'))
allwords=[(''.join(map(str,w)),feasible(w)) for w in itertools.product(range(4),repeat=5)]
for entry in cert:
    a,b=map(Q,entry['band']);allowed=set(entry['allowed_words'])
    expected={w for w,span in allwords if span is not None and span[0]<b and span[1]>a}
    assert expected==allowed
    ranks=entry['vertex_rank'];cycles=entry['cycles'];edges={}
    for cycle in cycles:
        assert len(cycle)==len(set(cycle))
        for i,v in enumerate(cycle):
            w=cycle[(i+1)%len(cycle)]
            assert v not in edges;edges[v]=w
            assert v[1:]==w[:-1]
            assert v+w[-1] in allowed
            assert ranks[v]==ranks[w]
    for word in allowed:
        v,w=word[:4],word[1:]
        assert ranks[v]<=ranks[w]
        if ranks[v]==ranks[w]:assert edges.get(v)==w
    print('VERIFIED',entry['band'],'words',len(allowed),'cycles',len(cycles))
print('All five open bands verified with exact rational arithmetic.')
