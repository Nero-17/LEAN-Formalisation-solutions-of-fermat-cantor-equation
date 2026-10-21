"""Run exact antichain certificate at an actual Fermat source slope."""
import json
import argparse
import sys
import math
from fractions import Fraction
from r003_digits_exact_antichain import run

if __name__ == "__main__":
    sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    parser.add_argument("--depth", type=int, default=30)
    parser.add_argument("--sources", default="work/r003_r004_transfer_sources.json")
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    source = next(row for row in json.load(open(args.sources)) if row["n"] == args.n)
    slope = Fraction(source["slope"])
    result = run(slope.numerator, slope.denominator, Fraction(1,100000), args.depth,
                 store_all=not args.compact)
    result["source"] = source
    result["amplified_lipschitz"] = str(3**result["depth"] * Fraction(source["lipschitz"]))
    result["transfer_passes"] = bool(result["complete"] and
        Fraction(result["amplified_lipschitz"]) < Fraction(1,100000))
    result["dimension_lower_bound"] = f"log(2)/({result['depth']}*log(3))" if result["transfer_passes"] else None
    result["dimension_lower_bound_decimal"] = math.log(2)/result["depth"]/math.log(3) if result["transfer_passes"] else None
    output = f"work/r003_digits_{'compact' if args.compact else 'actual'}_antichain_n{args.n}.json"
    json.dump(result, open(output,"w"), indent=2)
    print({"n":args.n, "complete":result["complete"], "depth":result["depth"],
           "transfer_passes":result["transfer_passes"], "output":output})
