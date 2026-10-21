"""Certified slope windows using correlated affine interval endpoints.

Each endpoint is (A*r+B)/denominator. Union merges only when overlap holds
throughout the slope interval. Intersections use rigorous affine inner bounds.
No sampling is used for validity; midpoint sorting only selects candidates.
"""
import argparse,json,hashlib
from fractions import Fraction
from itertools import combinations
from math import lcm

def run(lower,upper,margin,depth_limit=40,limit=2000000,components=(0,1,2),
        one_only=False,required_components=None,domain_inset=Fraction(0),
        weighted_error=None):
    parameter_denominator=lcm(lower.denominator,upper.denominator)
    parameter_lower=int(lower*parameter_denominator)
    parameter_upper=int(upper*parameter_denominator)
    def midpoint(endpoint):
        a,b=endpoint
        return a*(parameter_lower+parameter_upper)+2*b*parameter_denominator
    def maximum(endpoint):
        a,b=endpoint
        return max(a*parameter_lower+b*parameter_denominator,
                   a*parameter_upper+b*parameter_denominator)
    def minimum(endpoint):
        a,b=endpoint
        return min(a*parameter_lower+b*parameter_denominator,
                   a*parameter_upper+b*parameter_denominator)
    def difference(first,second):
        return first[0]-second[0],first[1]-second[1]
    def le(first,second):return maximum(difference(first,second))<=0
    def join(intervals):
        intervals=sorted(intervals,key=lambda pair:midpoint(pair[0]))
        out=[]
        for left,right in intervals:
            if out and le(left,out[-1][1]) and le(out[-1][0],right):
                previous_left,previous_right=out[-1]
                out[-1]=(previous_left if midpoint(previous_left)<=midpoint(left) else left,
                         previous_right if midpoint(previous_right)>=midpoint(right) else right)
            else:out.append((left,right))
        return out
    def inside_intersections(first,second):
        result=[];i=j=0
        while i<len(first) and j<len(second):
            left1,right1=first[i];left2,right2=second[j]
            left,other=(left1,left2) if midpoint(left1)>=midpoint(left2) else (left2,left1)
            correction=max(0,(maximum(difference(other,left))+parameter_denominator-1)//parameter_denominator)
            left=(left[0],left[1]+correction)
            right,other=(right1,right2) if midpoint(right1)<=midpoint(right2) else (right2,right1)
            correction=max(0,(maximum(difference(right,other))+parameter_denominator-1)//parameter_denominator)
            right=(right[0],right[1]-correction)
            if le(left,right):result.append((left,right))
            if midpoint(right1)<midpoint(right2):i+=1
            else:j+=1
        return result
    def scaled(intervals):
        return [((3*a,3*b),(3*c,3*d)) for (a,b),(c,d) in intervals]
    denominator=lcm(6,margin.denominator,domain_inset.denominator,10**12,
                    weighted_error.denominator if weighted_error is not None else 1)
    switch=[((0,denominator//3),(denominator//6,denominator//6)),
            ((denominator//3,0),(denominator//6,denominator//2)),
            ((denominator//3,denominator//3),(denominator//2,denominator//6))]
    inset=int(domain_inset*denominator)
    switch=[((a,b+inset),(c,d-inset)) for (a,b),(c,d) in switch]
    required=[switch[j] for j in (required_components if required_components is not None else components)]
    switch=[switch[j] for j in components]
    shrink=int((2*3**depth_limit*weighted_error if weighted_error is not None else margin)*denominator)
    one=[((a,b+shrink),(c,d-shrink)) for (a,b),(c,d) in switch]
    if weighted_error is not None:
        one=[(left,right) for left,right in one if le(left,right)]
    else:assert all(le(left,right) for left,right in one)
    first_allowed_stop=depth_limit if weighted_error is not None and one else None
    two=[];history=[];complete=False
    for depth in range(1,depth_limit+1):
        offsets=[(0,0),(0,denominator),(denominator,0),(denominator,denominator)]
        images_one=[[((a+u,b+v),(c+u,d+v)) for (a,b),(c,d) in one] for u,v in offsets]
        if not one_only:
            images_two=[[((a+u,b+v),(c+u,d+v)) for (a,b),(c,d) in two] for u,v in offsets]
            next_two=([] if weighted_error is not None else scaled(two))+[pair for group in images_two for pair in group]
            for i,j in combinations(range(4),2):
                next_two.extend(inside_intersections(images_one[i],images_one[j]))
            two=join(next_two)
        next_switch=scaled(switch)
        if weighted_error is not None:
            base=[((a,b+shrink),(c,d-shrink)) for (a,b),(c,d) in next_switch]
            base=[(left,right) for left,right in base if le(left,right)]
            if base and first_allowed_stop is None:first_allowed_stop=depth_limit-depth
        else:base=scaled(one)
        one=join(base+[pair for group in images_one for pair in group])
        denominator*=3;switch=next_switch;required=scaled(required)
        coverage_union=one if one_only else two
        witnesses=[]
        for left,right in required:
            witnesses.append(next((interval for interval in coverage_union
                                   if le(interval[0],left) and le(right,interval[1])),None))
        complete=all(w is not None for w in witnesses)
        row=dict(depth=depth,one_intervals=len(one),two_intervals=len(two),
                 covered_components=sum(w is not None for w in witnesses))
        if weighted_error is not None:row["backward_level"]=depth_limit-depth
        history.append(row);print(row,flush=True)
        if complete or len(one)+len(two)>limit:break
    digest=hashlib.sha256()
    for (a,b),(c,d) in coverage_union:digest.update(f"{a},{b},{c},{d}\n".encode("ascii"))
    return dict(lower=str(lower),upper=str(upper),margin=str(margin),components=list(components),
                target_margin_mode="length_weighted" if weighted_error is not None else "fixed",
                domain_inset=str(domain_inset),
                weighted_error=str(weighted_error) if weighted_error is not None else None,
                weighted_initial_depth=depth_limit if weighted_error is not None else None,
                certified_nonlinear_error=str(weighted_error*3**(depth_limit-depth)) if weighted_error is not None else None,
                return_length_bound=first_allowed_stop-(depth_limit-depth) if weighted_error is not None and first_allowed_stop is not None else depth,
                one_only=one_only,required_components=list(required_components) if required_components is not None else list(components),
                complete=complete,depth=depth,denominator=str(denominator),
                history=history,covering_affine_intervals=[
                    [[str(a),str(b)],[str(c),str(d)]] if w else None
                    for w in witnesses for a,b,c,d in
                    ([(*w[0],*w[1])] if w else [(0,0,0,0)])],
                two_affine_sha256=digest.hexdigest())

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--lower",required=True);parser.add_argument("--upper",required=True)
    parser.add_argument("--margin",default="1/100000");parser.add_argument("--depth",type=int,default=40)
    parser.add_argument("--component",type=int,choices=(0,1,2))
    parser.add_argument("--one-only",action="store_true")
    parser.add_argument("--required-component",type=int,choices=(0,1,2))
    parser.add_argument("--require-all",action="store_true")
    parser.add_argument("--domain-inset",default="0")
    parser.add_argument("--weighted-error")
    parser.add_argument("--output",required=True);args=parser.parse_args()
    result=run(Fraction(args.lower),Fraction(args.upper),Fraction(args.margin),args.depth,
               components=(args.component,) if args.component is not None else (0,1,2),
               one_only=args.one_only,
               required_components=(0,1,2) if args.require_all else (
                   (args.required_component,) if args.required_component is not None else None),
               domain_inset=Fraction(args.domain_inset),
               weighted_error=Fraction(args.weighted_error) if args.weighted_error else None)
    json.dump(result,open(args.output,"w"),indent=2)
    print({k:v for k,v in result.items() if k!="history"})
