from fractions import Fraction as F
from itertools import combinations
from math import lcm
from pathlib import Path
import json,sys

def union(intervals):
    result=[]
    for lo,hi in sorted(intervals):
        if result and lo<=result[-1][1]:result[-1]=(result[-1][0],max(hi,result[-1][1]))
        else:result.append((lo,hi))
    return result

def intersection(left,right):
    i=j=0;result=[]
    while i<len(left) and j<len(right):
        lo=max(left[i][0],right[j][0]);hi=min(left[i][1],right[j][1])
        if lo<=hi:result.append((lo,hi))
        if left[i][1]<right[j][1]:i+=1
        else:j+=1
    return result

def check(slope,maximum_depth=13):
    margin=F(1,100000)
    switches=[(F(1,3),(slope+1)/6),(slope/3,(slope+3)/6),((slope+1)/3,(3*slope+1)/6)]
    denominator=lcm(slope.denominator,margin.denominator,*[v.denominator for pair in switches for v in pair])
    target=[(int(lo*denominator),int(hi*denominator)) for lo,hi in switches]
    one=[(lo+int(margin*denominator),hi-int(margin*denominator)) for lo,hi in target]
    two=[];history=[]
    for depth in range(1,maximum_depth+1):
        offsets=[0,denominator,int(slope*denominator),int((1+slope)*denominator)]
        branch_one=[[(lo+offset,hi+offset) for lo,hi in one] for offset in offsets]
        next_two=[(3*lo,3*hi) for lo,hi in two]
        next_two.extend((lo+offset,hi+offset) for offset in offsets for lo,hi in two)
        for i,j in combinations(range(4),2):next_two.extend(intersection(branch_one[i],branch_one[j]))
        two=union(next_two)
        one=union([(3*lo,3*hi) for lo,hi in one]+[pair for branch in branch_one for pair in branch])
        denominator*=3;target=[(3*lo,3*hi) for lo,hi in target]
        covered=[any(lo<=left and right<=hi for lo,hi in two) for left,right in target]
        history.append([depth,len(one),len(two),sum(covered)])
        if all(covered):
            assert depth<=maximum_depth
            return {'slope':str(slope),'margin':str(margin),'depth':depth,'status':'PASS','history':history}
    raise AssertionError(slope)

if __name__=='__main__':
    results=[check(F(sys.argv[1]),int(sys.argv[2]))] if len(sys.argv)>1 else [check(F(13,10)),check(F(33,25))]
    output='work/thirdreal20261021_adversarial_returns_87_verified.json' if len(sys.argv)>1 else 'work/thirdreal20261021_adversarial_returns_verified.json'
    Path(output).write_text(json.dumps(results,indent=2))
    print(json.dumps(results,indent=2))
