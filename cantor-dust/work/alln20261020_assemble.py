"""Assemble the exact range coverage AFTER all substantive verifiers pass.

This checks range unions and binds reports to their integer candidate files.
It does not replace the mathematical proofs or arithmetic verifiers.
"""
from pathlib import Path
from fractions import Fraction as F
import json
import hashlib
from datetime import datetime, timezone

work=Path("work")

def read(name):
    return json.loads((work/name).read_text(encoding="utf-8"))

def bind(report_name,candidate_name,status_key="status"):
    report=read(report_name)
    assert report[status_key]=="PASS",(report_name,"not PASS")
    digest=hashlib.sha256((work/candidate_name).read_bytes()).hexdigest()
    assert report["input_sha256"]==digest,(report_name,"candidate changed")
    return report,digest

records=[]
baseline=read("r003_parent_finite_coverage.json")
assert baseline["verified_range"]==[2,300] and baseline["integer_count"]==299
assert baseline["missing"]==[]
records.append(dict(range=[2,300],kind="previously proved source and return certificates",
                    report="r003_parent_finite_coverage.json",
                    report_sha256=hashlib.sha256((work/"r003_parent_finite_coverage.json").read_bytes()).hexdigest()))
for report_name,candidate_name,expected in [
    ("alln20261020_parent_complete_301_10000_verified.json",
     "alln20261020_logsource_complete_301_10000.json",[301,10000]),
    ("alln20261020_parent_10001_50000_verified.json",
     "alln20261020_parent_logsource_10001_50000.json",[10001,50000]),
    ("alln20261020_parent_50001_177146_verified.json",
     "alln20261020_batch_50001_177146.json",[50001,177146]),
    ("alln20261020_parent_177147_531440_verified.json",
     "alln20261020_batch_177147_531440.json",[177147,531440]),
]:
    report,digest=bind(report_name,candidate_name)
    assert report["range"]==expected and not report["missing"]
    assert report["checked"]==expected[1]-expected[0]+1
    rows=read(candidate_name)["rows"]
    assert sorted(row["n"] for row in rows)==list(range(expected[0],expected[1]+1))
    records.append(dict(range=expected,kind="strict exact logarithmic sources",
                        report=report_name,candidate=candidate_name,input_sha256=digest))

fixed_pieces=[]
for m in (12,13,14):
    if (work/f"alln20261020_fixed_m{m}_verified.json").exists():
        fixed_pieces.append((m,"",["1","3"]))
    else:
        fixed_pieces.extend([(m,"_lower",["1","2"]),(m,"_upper",["2","3"])])
for m,suffix,domain in fixed_pieces:
    report_name=f"alln20261020_fixed_m{m}{suffix}_verified.json"
    candidate_name=f"alln20261020_fixed_m{m}{suffix}_candidate.json"
    report,digest=bind(report_name,candidate_name,"verification")
    assert report["m"]==m and report["parameter_domain"]==domain
    data=read(candidate_name)
    assert data["m"]==m and not data["failures"]
    intervals=[(F(*r["t_lower"]),F(*r["t_upper"])) for r in data["cells"]]
    right=F(domain[0])
    for lo,hi in sorted(intervals):
        assert lo<=right and lo<hi
        right=max(right,hi)
    assert right==F(domain[1])
    lo=3**m*F(domain[0])
    hi=min(3**(m+1)-1,3**m*F(domain[1]))
    assert lo.denominator==1 and F(hi).denominator==1
    expected=[int(lo),int(hi)]
    assert report["integer_range"]==expected
    records.append(dict(range=expected,kind="whole fixed-scale parameter interval",
                        report=report_name,candidate=candidate_name,input_sha256=digest))

tail,tail_digest=bind("alln20261020_parent_finite_m15_verified.json",
                      "alln20261020_finite_z_m15_h3_depth11.json")
assert tail["minimum_m"]==15 and tail["minimum_n"]==3**15
assert tail["endpoint_depth"]+3<=15
tail_agent,_=bind("alln20261020_finite_z_m15_depth11_verified.json",
                  "alln20261020_finite_z_m15_h3_depth11.json","verification")
assert tail_agent["minimum_n"]==3**15

end=1
for row in sorted(records,key=lambda r:r["range"]):
    left,right=row["range"]
    assert left<=end+1,("integer gap",end,left)
    end=max(end,right)
assert end+1==3**15
records.append(dict(range=[3**15,"infinity"],kind="uniform finite-scale full-phase theorem",
                    report="alln20261020_parent_finite_m15_verified.json",
                    candidate="alln20261020_finite_z_m15_h3_depth11.json",
                    input_sha256=tail_digest))
result=dict(status="PASS",conclusion="Every integer n>=2 has an uncountable, indeed positive-Hausdorff-dimensional Fermat intersection in C^2.",
            n_equals_one="The reflected graph {(x,1-x):x in C}; dimension log(2)/log(3).",
            coverage=records,integer_gap=None,
            complete_utc=datetime.now(timezone.utc).isoformat(),
            scope="Coverage assembly and input integrity, relying on the already executed exact source/phase/return verifiers and the written transfer proof.")
(work/"alln20261020_all_integer_coverage.json").write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
