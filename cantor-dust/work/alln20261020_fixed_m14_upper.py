"""Discover the m=14 fixed phase cover on 2<=t<=3; numerical only."""
import json
import time
from pathlib import Path
from alln20261020_fixed_m_phase import good_interval,prefixes

def discover(step=1000):
    started=time.monotonic()
    old=json.loads(Path("work/alln20261020_selected_cover.json").read_text())
    endpoints=list(dict.fromkeys([r["P"] for r in old["t_cover"]]+
                    [round(float(x)*19683) for x in prefixes(6) if x>=2/3-1e-12]))
    recent=endpoints.copy();cells=[];failures=[]
    stack=[(k,step,0) for k in range(3*step-1,2*step-1,-1)]
    while stack:
        k,den,level=stack.pop()
        lo,hi=k/den,(k+1)/den
        preferred=[r["P"] for r in old["t_cover"]
                   if r["t_interval"][0]<=(lo+hi)/2<=r["t_interval"][1]]
        order=list(dict.fromkeys(preferred+recent))
        chosen=None
        for P in order:
            if good_interval(lo,hi,14,P,9):
                chosen=P;break
        if chosen is not None:
            cells.append({"t_lower":[k,den],"t_upper":[k+1,den],"P":chosen})
            recent.remove(chosen);recent.insert(0,chosen)
        elif level<8:
            stack.extend([(2*k+1,2*den,level+1),(2*k,2*den,level+1)])
        else:failures.append([lo,hi])
        if len(cells) and len(cells)%200==0:
            Path("work/alln20261020_fixed_m14_upper_progress.json").write_text(
                json.dumps(dict(cells=cells,failures=failures,stack=stack)))
            print(14,len(cells),len(stack),len(failures),
                  round(time.monotonic()-started,1),flush=True)
    result=dict(status="floating candidate only",m=14,endpoint_depth=9,height=3,
                v_depth=4,inset=1e-9,cells=cells,failures=failures,
                parameter_domain=["2","3"],elapsed_seconds=time.monotonic()-started)
    Path("work/alln20261020_fixed_m14_upper_candidate.json").write_text(json.dumps(result,indent=2))
    print("DONE",len(cells),"failures",len(failures),flush=True)

if __name__=="__main__":discover()
