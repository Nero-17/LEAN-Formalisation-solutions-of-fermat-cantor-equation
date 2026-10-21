"""Exact adaptive interval proof of weighted antichain returns."""
import argparse,json,math,time
from fractions import Fraction
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument("--beta",default="11/10")
ap.add_argument("--depth",type=int,default=24)
ap.add_argument("--limit",type=int,default=200000)
ap.add_argument("--save",default="work/branching_r010_adaptive")
ap.add_argument("--N",type=int,default=10**12)
ap.add_argument("--core",default="middle")
ap.add_argument("--extra-depth",type=int,default=0)
ap.add_argument("--every",type=int,default=1000)
ap.add_argument("--middle-weight",default="1")
ap.add_argument("--probe",type=int,default=0)
ap.add_argument("--resume")
ap.add_argument("--source-file")
ap.add_argument("--source-index",type=int,default=0)
ap.add_argument("--margin",default="1/100000")
ap.add_argument("--cut",default="",help="Comma-separated left:right intervals, also reflected.")
args=ap.parse_args()
margin=Fraction(args.margin)
assert margin>0
P,Q=1050654887606011358,11741973776954721170
target=3**80
quadratic_coefficient=Fraction(9)
source_a_level,source_b_level=40,39
custom_source=None
if args.source_file:
    custom_source=json.loads(Path(args.source_file).read_text())["sources"][args.source_index]
    P,Q,target=custom_source["P"],custom_source["Q"],custom_source["target"]
    source_level=custom_source["level"]
    source_a_level=custom_source.get("a_level",source_level+1)
    source_b_level=custom_source.get("b_level",source_level)
    quadratic_coefficient=Fraction(custom_source.get("quadratic_coefficient","9"))
    assert target==3**(2*source_a_level)
    assert quadratic_coefficient==Fraction(3)**(2*(source_a_level-source_b_level))
    def valid_ternary(value,length):
        for _ in range(length):
            value,digit=divmod(value,3)
            if digit not in (0,2):return False
        return value==0
    assert valid_ternary(P,source_b_level) and valid_ternary(Q,source_a_level)
    assert quadratic_coefficient*P*P+Q*Q<=target<=quadratic_coefficient*(P+1)**2+(Q+1)**2
source_word=[]
if args.extra_depth:
    sources=[(P,Q,[])]
    for level in range(args.extra_depth):
        target*=9
        next_sources=[]
        for horizontal,vertical,word in sources:
            for dx in (0,2):
                for dy in (0,2):
                    xx,yy=3*horizontal+dx,3*vertical+dy
                    if quadratic_coefficient*xx**2+yy**2<=target<=quadratic_coefficient*(xx+1)**2+(yy+1)**2:
                        next_sources.append((xx,yy,word+[(dx,dy)]))
        sources=next_sources
    if args.core in ("central","root","around_root"):
        preferred={"central":Fraction(58,100),"root":Fraction(64,100),
                   "around_root":Fraction(645,1000)}[args.core]
        sources.sort(key=lambda item:abs((target-quadratic_coefficient*item[0]**2-item[1]**2)/(4*quadratic_coefficient*item[0])-preferred))
    for horizontal,vertical,word in sources:
        candidate_r=vertical/(quadratic_coefficient*horizontal)
        candidate_t=(target-quadratic_coefficient*horizontal**2-vertical**2)/(4*quadratic_coefficient*horizontal)
        if candidate_r/3+margin<candidate_t<(candidate_r+3)/6-margin:
            P,Q,source_word=horizontal,vertical,word
            break
    else:
        raise RuntimeError("No deeper source in the middle core.")
r=Q/(quadratic_coefficient*P);N=args.N;scale=10000
beta=Fraction(args.beta);size=math.ceil((r+1)*N/2)+2
full=[(Fraction(1,3),(r+1)/6),(r/3,(r+3)/6),((r+1)/3,(3*r+1)/6)]
available={"B":full,"middle":[full[1]],
           "central":[(Fraction(48,100),Fraction(68,100))],
           "root":[(Fraction(60,100),Fraction(68,100))],
           "around_root":[(Fraction(63,100),Fraction(66,100))]}
intervals=available[args.core]
cuts=[]
if args.cut:
    assert args.core=="B"
    for item in args.cut.split(","):
        left,right=map(Fraction,item.split(":"))
        assert left<right
        cuts.extend([(left,right),((r+1)/2-right,(r+1)/2-left)])
    for cut_left,cut_right in sorted(cuts):
        pieces=[]
        for left,right in intervals:
            if cut_right<=left or right<=cut_left:
                pieces.append((left,right))
            else:
                if left<cut_left:pieces.append((left,cut_left))
                if cut_right<right:pieces.append((cut_right,right))
        intervals=pieces
source_intercept=(target-quadratic_coefficient*P**2-Q**2)/(4*quadratic_coefficient*P)
assert any(left+margin<source_intercept<right-margin
           for left,right in intervals)
core=[(math.ceil((left+margin)*N),
       math.floor((right-margin)*N)) for left,right in intervals]
middle_weight=Fraction(args.middle_weight)
assert (scale*middle_weight).denominator==1 and middle_weight>0
weights=[int(scale*middle_weight) if full[1][0]<(left+right)/2<full[1][1] else scale
         for left,right in intervals] if args.core=="B" else [scale]*len(core)
offsets=[math.floor(d*N) for d in [0,1,r,r+1]]
error=3*(1+quadratic_coefficient)*N/(2*quadratic_coefficient*P)
assert error<1
assert all(d*N==math.floor(d*N) or error<1-(d*N-math.floor(d*N)) for d in [0,1,r,r+1])
calls=0

def value(lo,hi,remaining,cap):
    global calls
    calls+=1
    if lo<0 or hi>size or lo>=hi:
        return 0
    baseline=max((weights[index] if a<=lo and hi<=b else 0)
                 for index,(a,b) in enumerate(core))
    if baseline>=cap:
        return cap
    if remaining==0:
        return baseline
    needed=(cap*beta.numerator+beta.denominator-1)//beta.denominator
    total=0
    for off in offsets:
        total+=value(3*lo-off-1,3*hi-off+1,remaining-1,needed-total)
        if total>=needed:
            return cap
    return max(baseline,total*beta.denominator//beta.numerator)

if args.probe:
    probe_rows=[];begin=time.time()
    for index,(left,right) in enumerate(intervals):
        left_index,right_index=math.floor(left*N),math.floor(right*N)
        for j in range(args.probe+1):
            at=left_index+(right_index-left_index)*j//args.probe
            bound=value(at,at+1,args.depth,weights[index]+1)
            if bound<=weights[index]:
                probe_rows.append(dict(type=index,at=at,bound=bound,required=weights[index]+1))
                if len(probe_rows)>=10:break
    result=dict(status="FINITE_POINT_PROBES_ONLY",beta=str(beta),depth=args.depth,N=N,
                middle_weight=str(middle_weight),failures=probe_rows,calls=calls,
                elapsed=time.time()-begin,P=P,Q=Q,source_word=source_word,
                custom_source=custom_source,margin=str(margin),
                quadratic_coefficient=str(quadratic_coefficient),
                cuts=[[str(a),str(b)] for a,b in cuts])
    Path(args.save+".json").write_text(json.dumps(result,indent=2))
    print(json.dumps(result),flush=True)
    raise SystemExit
pending=[(math.floor(left*N),math.floor(right*N)+1,index)
         for index,(left,right) in reversed(list(enumerate(intervals)))]
accepted=[];failed=[];begin=time.time();tested=0;previous_elapsed=0
if args.resume:
    previous=json.loads(Path(args.resume).read_text())
    assert previous["beta"]==str(beta) and previous["N"]==N
    assert previous["depth"]==args.depth and previous["P"]==P and previous["Q"]==Q
    assert previous["core_interior"]==[list(pair) for pair in core]
    assert previous["terminal_weights"]==weights
    assert not previous["failed_intervals"]
    pending=[tuple(item) for item in previous["pending_intervals"]]
    accepted=[tuple(item) for item in previous["accepted_intervals"]]
    tested=previous["tested"];calls=previous["calls"]
    previous_elapsed=previous["elapsed"]
while pending and tested<args.limit:
    lo,hi,kind=pending.pop();tested+=1
    bound=value(lo,hi,args.depth,weights[kind]+1)
    if bound>weights[kind]:
        accepted.append((lo,hi))
    elif hi-lo<=1:
        failed.append((lo,hi));break
    else:
        middle=(lo+hi)//2
        pending.append((middle,hi,kind));pending.append((lo,middle,kind))
    if tested%args.every==0:
        print(json.dumps(dict(tested=tested,accepted=len(accepted),pending=len(pending),
                             calls=calls,current=[lo,hi],elapsed=previous_elapsed+time.time()-begin)),flush=True)
result=dict(status="CERTIFIED" if not pending and not failed else "INCOMPLETE",
            beta=str(beta),N=N,scale=scale,depth=args.depth,
            core=[[str(left),str(right)] for left,right in intervals],core_interior=core,
            tested=tested,calls=calls,elapsed=previous_elapsed+time.time()-begin,
            accepted_intervals=accepted,pending_intervals=pending,failed_intervals=failed,
            one_step_error_times_N=str(error),P=P,Q=Q,
            source_target=target,source_extra_depth=args.extra_depth,
            source_word=source_word,
            source_intercept=str(source_intercept),terminal_weights=weights,
            middle_weight=str(middle_weight),custom_source=custom_source,margin=str(margin),
            quadratic_coefficient=str(quadratic_coefficient),
            source_a_level=source_a_level+args.extra_depth,
            source_b_level=source_b_level+args.extra_depth,
            cuts=[[str(a),str(b)] for a,b in cuts])
Path(args.save+".json").write_text(json.dumps(result,indent=2))
print(json.dumps({k:v for k,v in result.items() if not k.endswith("_intervals")}),flush=True)
