"""R003 exact non-grid antichain tests.

Adapted without mathematical changes from the R004
2026-10-20/new-chat/work/agent2_exact_returns.py.
"""
import argparse
import hashlib
import json
import time
from fractions import Fraction
from itertools import combinations


def union(intervals):
    intervals=sorted(intervals)
    out=[]
    for a,b in intervals:
        if out and a<=out[-1][1]:
            if b>out[-1][1]:out[-1]=(out[-1][0],b)
        else:out.append((a,b))
    return out


def intersect(first,second):
    out=[];i=j=0
    while i<len(first) and j<len(second):
        a=max(first[i][0],second[j][0]);b=min(first[i][1],second[j][1])
        if a<=b:out.append((a,b))
        if first[i][1]<second[j][1]:i+=1
        else:j+=1
    return out


def covers(intervals,targets):
    return all(any(a<=u and v<=b for a,b in intervals) for u,v in targets)


def run(p,q,epsilon,maxdepth,store_all=True,components=(0,1,2),domain_inset=Fraction(0)):
    r=Fraction(p,q)
    switch=[(Fraction(1,3),(r+1)/6),
            (r/3,(r+3)/6),
            ((r+1)/3,(3*r+1)/6)]
    switch=[(switch[j][0]+domain_inset,switch[j][1]-domain_inset) for j in components]
    from math import lcm
    denominator=lcm(*(x.denominator for pair in switch for x in pair),
                    epsilon.denominator,q)
    switch=[(int(a*denominator),int(b*denominator)) for a,b in switch]
    shrink=int(epsilon*denominator)
    target=[(a+shrink,b-shrink) for a,b in switch]
    one=target;two=[];history=[]
    for depth in range(1,maxdepth+1):
        digit=[0,denominator,denominator*p//q,denominator*(p+q)//q]
        images_one=[[(a+d,b+d) for a,b in one] for d in digit]
        images_two=[[(a+d,b+d) for a,b in two] for d in digit]
        out_two=[(3*a,3*b) for a,b in two]
        for images in images_two:out_two.extend(images)
        for i,j in combinations(range(4),2):
            out_two.extend(intersect(images_one[i],images_one[j]))
        two=union(out_two)
        one=union([(3*a,3*b) for a,b in one]+[pair for images in images_one for pair in images])
        denominator*=3
        switch=[(3*a,3*b) for a,b in switch]
        complete=covers(two,switch)
        missing_length=sum(v-u for u,v in switch)-sum(b-a for a,b in intersect(two,switch))
        row={"depth":depth,"one_intervals":len(one),"two_intervals":len(two),
             "missing_length":float(Fraction(missing_length,denominator))}
        history.append(row)
        print(row,flush=True)
        if complete:break
        if len(one)+len(two)>2000000:break
    digest=hashlib.sha256()
    for a,b in two:
        digest.update(f"{a},{b}\n".encode("ascii"))
    witnesses=[(a,b) for a,b in two if any(a<=u<=v<=b for u,v in switch)]
    return {"slope":f"{p}/{q}","target_margin":str(epsilon),"complete":complete,
            "components":list(components),"domain_inset":str(domain_inset),
            "depth":depth,"denominator":str(denominator),"history":history,
            "all_two_intervals_sha256_ascii_comma_newline":digest.hexdigest(),
            "covering_intervals":[[str(a),str(b)] for a,b in witnesses],
            "two_cover":[[str(a),str(b)] for a,b in two] if complete and store_all else None}


if __name__=="__main__":
    a=argparse.ArgumentParser()
    a.add_argument("--p",type=int,default=1243)
    a.add_argument("--q",type=int,default=1000)
    a.add_argument("--epsilon",default="1/100000")
    a.add_argument("--depth",type=int,default=30)
    a.add_argument("--component",type=int,choices=(0,1,2))
    a.add_argument("--domain-inset",default="0")
    a.add_argument("--compact",action="store_true")
    a.add_argument("--output")
    args=a.parse_args()
    start=time.time()
    result=run(args.p,args.q,Fraction(args.epsilon),args.depth,store_all=not args.compact,
               components=(args.component,) if args.component is not None else (0,1,2),
               domain_inset=Fraction(args.domain_inset))
    result["elapsed"]=time.time()-start
    with open(args.output or f"work/r003_digits_exact_antichain_{args.p}_{args.q}.json","w") as f:json.dump(result,f,indent=2)
    print({k:v for k,v in result.items() if k not in ("history","two_cover")})
