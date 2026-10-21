"""Exact scalar strict-return DP with streaming unions and a recorded cap."""
from fractions import Fraction as F
from math import lcm
from itertools import combinations
from heapq import merge
import time

def joined(streams):
    out=[]
    for left,right in merge(*streams):
        if out and left<=out[-1][1]:
            if right>out[-1][1]:out[-1]=(out[-1][0],right)
        else:out.append((left,right))
    return out

def intersect(first,second):
    i=j=0
    while i<len(first) and j<len(second):
        left=max(first[i][0],second[j][0]);right=min(first[i][1],second[j][1])
        if left<=right:yield left,right
        if first[i][1]<second[j][1]:i+=1
        else:j+=1

def shifted(intervals,offset):
    return ((left+offset,right+offset) for left,right in intervals)

def check(r,maximum_depth=22,cap=700000,margin=F(1,100000),components=(0,1,2),inset=F(0),levels=None):
    switches=[(F(1,3),(r+1)/6),(r/3,(r+3)/6),((r+1)/3,(3*r+1)/6)]
    switches=[(switches[index][0]+inset,switches[index][1]-inset) for index in components]
    if levels is not None:switches=levels
    assert all(left+2*margin<right for left,right in switches)
    den=lcm(r.denominator,margin.denominator,*[x.denominator for pair in switches for x in pair])
    target=[(int(left*den),int(right*den)) for left,right in switches]
    one=[(left+int(margin*den),right-int(margin*den)) for left,right in target];two=[];history=[]
    start=time.monotonic()
    for depth in range(1,maximum_depth+1):
        offsets=[0,den,int(r*den),int((r+1)*den)]
        branches=[list(shifted(one,offset)) for offset in offsets]
        streams=[((3*left,3*right) for left,right in two)]
        streams.extend(shifted(two,offset) for offset in offsets)
        streams.extend(intersect(branches[i],branches[j]) for i,j in combinations(range(4),2))
        new_two=joined(streams)
        new_one=joined([((3*left,3*right) for left,right in one)]+branches)
        two,one=new_two,new_one;den*=3;target=[(3*left,3*right) for left,right in target]
        covered=[any(left<=a and b<=right for left,right in two) for a,b in target]
        history.append([depth,len(one),len(two),sum(covered)])
        if all(covered) or len(one)+len(two)>cap:break
    gaps=[]
    for index,(left,right) in enumerate(target):
        cursor=left
        for low,high in two:
            if high<cursor:continue
            if low>right:break
            if low>cursor:gaps.append((index,cursor,min(low,right)))
            cursor=max(cursor,high)
            if cursor>=right:break
        if cursor<right:gaps.append((index,cursor,right))
    return {'slope':str(r),'margin':str(margin),'components':list(components),'domain_inset':str(inset),'target_levels':[[str(a),str(b)] for a,b in switches],'complete':all(covered),'depth':depth,
            'missing_count':len(gaps),'missing_largest':[[i,str(F(lo,den)),str(F(hi,den))] for i,lo,hi in sorted(gaps,key=lambda x:x[2]-x[1],reverse=True)[:50]],
            'history':history,'elapsed':time.monotonic()-start,'cap':cap}
