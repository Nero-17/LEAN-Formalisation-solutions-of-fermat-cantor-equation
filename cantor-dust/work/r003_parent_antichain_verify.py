"""Independent exact event-sweep verifier; no imports from generators.

The producer uses six pairwise list intersections. Here multiplicity is
reconstructed from closed endpoint events, including singleton overlaps.
"""
from fractions import Fraction as F
from pathlib import Path
from math import lcm,log
import argparse,json,hashlib,time,sys
sys.set_int_max_str_digits(0)

def coverage(intervals,threshold=1):
    events={}
    for a,b in intervals:
        assert a<=b
        events.setdefault(a,[0,0])[0]+=1
        events.setdefault(b,[0,0])[1]+=1
    out=[];active=0;start=None
    for x,(begins,ends) in sorted(events.items()):
        at=active+begins
        after=at-ends
        if active<threshold<=at:start=x
        if after<threshold<=at:
            assert start is not None
            out.append((start,x));start=None
        active=after
    assert active==0 and start is None
    return out

def check_prefix(integer,depth):
    assert 0<=integer<3**depth
    for _ in range(depth):
        assert integer%3 in (0,2)
        integer//=3
    assert integer==0

def main(n,compact=False):
    started=time.time()
    path=Path(f"work/r003_digits_{'compact' if compact else 'actual'}_antichain_n{n}.json")
    data=json.loads(path.read_text())
    source=data["source"]
    P,Q,p,q=(int(source[k]) for k in ("P","Q","p","q"))
    assert n==source["n"] and q>=p
    check_prefix(P,p);check_prefix(Q,q)
    scale=3**(n*(q-p))
    target=3**(n*q)
    assert scale*P**n+Q**n<target<scale*(P+1)**n+(Q+1)**n
    slope=F(Q**(n-1),scale*P**(n-1))
    intercept=F(target-scale*P**n-Q**n,2*n*scale*P**(n-1))
    error=F((Q+1)**(n-1)-Q**(n-1),2*scale*P**(n-1))
    error+=F((P+1)**(n-1)-P**(n-1),2*P**(n-1))
    actual_slope=slope
    if "actual_slope" in source:
        assert actual_slope==F(source["actual_slope"])
        slope=F(source["slope"])
        assert slope<=actual_slope
        error+=(actual_slope-slope)/2
    assert slope==F(source["slope"])==F(data["slope"])
    assert str(intercept)==source["intercept"]
    assert str(error)==source["lipschitz"]
    assert 1<slope<3
    switch=[(F(1,3),(slope+1)/6),(slope/3,(slope+3)/6),
            ((slope+1)/3,(3*slope+1)/6)]
    assert any(a<intercept<b for a,b in switch)
    margin=F(data["target_margin"])
    denominator=lcm(slope.denominator,margin.denominator,
                    *(x.denominator for ab in switch for x in ab))
    switch=[(int(a*denominator),int(b*denominator)) for a,b in switch]
    one=[(a+int(margin*denominator),b-int(margin*denominator)) for a,b in switch]
    assert all(a<b for a,b in one)
    two=[];history=[]
    for depth in range(1,data["depth"]+1):
        offsets=[0,denominator,int(slope*denominator),int((slope+1)*denominator)]
        # one is a disjoint union with no touching components. Thus >=2
        # image multiplicity necessarily uses different first digits.
        assert all(one[j][1]<one[j+1][0] for j in range(len(one)-1))
        pairs=coverage(((a+d,b+d) for d in offsets for a,b in one),2)
        new_two=coverage(pairs+[(a+d,b+d) for d in offsets for a,b in two]
                         +[(3*a,3*b) for a,b in two])
        new_one=coverage([(a+d,b+d) for d in offsets for a,b in one]
                         +[(3*a,3*b) for a,b in one])
        one,two=new_one,new_two
        denominator*=3
        switch=[(3*a,3*b) for a,b in switch]
        covered=all(any(a<=u<=v<=b for a,b in two) for u,v in switch)
        row=[depth,len(one),len(two),covered]
        history.append(row);print(n,row,flush=True)
        assert len(one)==data["history"][depth-1]["one_intervals"]
        assert len(two)==data["history"][depth-1]["two_intervals"]
    assert covered and data["complete"]
    assert str(denominator)==data["denominator"]
    digest=hashlib.sha256()
    for a,b in two:
        digest.update(f"{a},{b}\n".encode("ascii"))
    if compact:
        assert digest.hexdigest()==data["all_two_intervals_sha256_ascii_comma_newline"]
        for a,b in data["covering_intervals"]:
            assert (int(a),int(b)) in two
    else:
        expected=data.pop("two_cover")
        assert len(expected)==len(two)
        for pair,(a,b) in zip(expected,two):
            assert pair==[str(a),str(b)]
    assert 3**depth*error<margin
    output=dict(n=n,verification="PASS",source=source,
                method="independent closed endpoint event sweep",
                return_depth=depth,return_margin=str(margin),
                amplified_lipschitz=str(3**depth*error),
                every_endpoint_matches=True,history=history,
                all_two_intervals_sha256_ascii_comma_newline=digest.hexdigest(),
                hausdorff_lower_bound=f"log(2)/({depth}*log(3))",
                dimension_decimal=log(2)/(depth*log(3)),
                elapsed_seconds=time.time()-started,
                certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    Path(f"work/r003_parent_antichain_verify_n{n}.json").write_text(json.dumps(output,indent=2))
    print({k:v for k,v in output.items() if k not in ("source","history","amplified_lipschitz")},flush=True)

if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--n",required=True,type=int)
    parser.add_argument("--compact",action="store_true")
    args=parser.parse_args()
    main(args.n,args.compact)
