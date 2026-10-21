"""Exact rational verification for the all-index two-axis interval family."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json


def add(*terms):
    out = [F(0)]*max(map(len,terms))
    for term in terms:
        for j,c in enumerate(term):
            out[j] += c
    return out


def scale(term,c):
    return [F(c)*v for v in term]


def multiply(a,b):
    out = [F(0)]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        for k,y in enumerate(b):
            out[j+k] += x*y
    return out


def shifted(a,n):
    return [F(0)]*n+a


def evaluate(a,x):
    return sum(c*x**j for j,c in enumerate(a))


def bernstein(a,left,right):
    degree=len(a)-1
    power=[sum(a[j]*comb(j,i)*left**(j-i)*(right-left)**i
               for j in range(i,degree+1)) for i in range(degree+1)]
    return [sum(power[j]*F(comb(i,j),comb(degree,j)) for j in range(i+1))
            for i in range(degree+1)]


def verify():
    left,right=F(2679,10000),F(67,250)
    one_minus=[F(1),F(-1)]
    square=multiply(one_minus,one_minus)
    lambda_two_minus=[F(0),F(2),F(-1)]
    outer_shift=multiply(one_minus,lambda_two_minus)
    nested_lower=add(outer_shift,shifted([F(2),F(-1)],3))
    nested_upper=add(outer_shift,shifted(square,2))
    constraints={
        "root_derivative": [F(4),F(-2)]+[F(0)]*5+[F(-8*381,100)],
        "earlier_scale_excluded": [F(1),F(0),F(-381,100)],
        "X_cylinder_forced": add(scale(square,2),[F(0),F(0),F(-381,100)]),
        "Y_cylinder_forced": [F(2),F(-2),F(-381,100)],
        "first_projection_gap": add(square,scale(lambda_two_minus,-1)),
        "nested_gap_below_other_first_children": add(square,scale(nested_upper,-1)),
        "nested_gap_above_other_second_children": add(square,scale(outer_shift,-1)),
        "tail_above_gap": add([F(0),F(379,200),F(0),F(-1,2)],
                              shifted([F(-1,2)],7),scale(lambda_two_minus,-1)),
        "tail_below_gap": add(square,[F(0),F(-381,200)],
                              shifted([F(-1)],7)),
        "first_scale_above_nested_gap": add([F(0),F(279,200)],
                                           shifted([F(-1,2)],7),
                                           scale(nested_lower,-1)),
        "first_scale_below_nested_gap": add(nested_upper,[F(0),F(-281,200)],
                                           shifted([F(-1)],7)),
        "near_axis_same_right_excluded": add(scale(square,2),[F(-1)]),
        "near_axis_low_exponent_excluded": add(multiply(one_minus,[F(2),F(-1)]),[F(-1)]),
        "near_axis_high_exponent_excluded": add(square,[F(0),F(0),F(-2)]),
    }
    checks=[]
    for name,poly in constraints.items():
        bounds=bernstein(poly,left,right)
        assert min(bounds)>0,(name,min(bounds))
        checks.append({"name":name,"coefficients":list(map(str,poly)),
                       "minimum_Bernstein_coefficient":str(min(bounds))})
    left_defect=4*left-1-left*left
    right_defect=4*right-1-right*right-F(381,100)*right**8
    assert left_defect<0 and right_defect>0
    result={"scope":"Exact all-index theorem, not finite extrapolation",
            "n":">=3","lambda_container":[str(left),str(right)],
            "scaled_parameter":[str(F(379,100)),str(F(381,100))],
            "left_defect":str(left_defect),"right_defect":str(right_defect),
            "checks":checks,"verified":True}
    print("All exact rational checks passed.")
    for c in checks:
        print(c["name"],float(F(c["minimum_Bernstein_coefficient"])))
    return result


if __name__=="__main__":
    result=verify()
    Path("work/r008_evidence_gap_family.json").write_text(json.dumps(result,indent=2))
