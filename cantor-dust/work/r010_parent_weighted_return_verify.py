"""Independent exact rational antichain verifier for the adaptive interval cover.

At remaining depth h, return the numerator over beta.numerator**h.
Unlike the discovery DP, there is no rounding of capacities to a fixed scale.
"""
import argparse
import hashlib
import json
import math
import time
from fractions import Fraction
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("certificate")
parser.add_argument("--output", default="work/r010_parent_weighted_return_verify.json")
args = parser.parse_args()
source = Path(args.certificate)
certificate = json.loads(source.read_text(encoding="utf-8"))
assert certificate["status"] == "CERTIFIED"
assert not certificate["pending_intervals"]
assert not certificate["failed_intervals"]
beta = Fraction(certificate["beta"])
grid = certificate["N"]
depth = certificate["depth"]
P = certificate.get("P", 1050654887606011358)
Q = certificate.get("Q", 11741973776954721170)
extra_depth = certificate.get("source_extra_depth", 0)
custom_source = certificate.get("custom_source")
if custom_source:
    source_level = custom_source["level"]
    assert isinstance(source_level, int) and source_level >= 1
    a_level = custom_source.get("a_level", source_level + 1)
    b_level = custom_source.get("b_level", source_level)
    assert (custom_source["P"], custom_source["Q"]) == (P, Q)
    assert extra_depth == 0 and certificate.get("source_word", []) == []
else:
    source_level = 39 + extra_depth
    a_level, b_level = source_level + 1, source_level
assert isinstance(a_level, int) and isinstance(b_level, int)
assert a_level > 0 and b_level > 0
quadratic_coefficient = Fraction(3) ** (2 * (a_level - b_level))
if custom_source:
    assert Fraction(custom_source.get("quadratic_coefficient", "9")) == quadratic_coefficient
target_radius_squared = 3 ** (2 * a_level)
if custom_source:
    assert custom_source["target"] == target_radius_squared
if "source_target" in certificate:
    assert certificate["source_target"] == target_radius_squared
if extra_depth:
    horizontal, vertical = 1050654887606011358, 11741973776954721170
    word = certificate["source_word"]
    assert len(word) == extra_depth
    for dx, dy in word:
        assert dx in (0, 2) and dy in (0, 2)
        horizontal, vertical = 3 * horizontal + dx, 3 * vertical + dy
    assert (horizontal, vertical) == (P, Q)
for prefix, length in [(P, b_level), (Q, a_level)]:
    quotient = prefix
    for _ in range(length):
        quotient, digit = divmod(quotient, 3)
        assert digit in (0, 2)
    assert quotient == 0
assert P > 0 and Q > 0
ratio = Q / (quadratic_coefficient * P)
domains = [
    (Fraction(1, 3), (ratio + 1) / 6),
    (ratio / 3, (ratio + 3) / 6),
    ((ratio + 1) / 3, (3 * ratio + 1) / 6),
]
assert certificate["core"] == [[str(a), str(b)] for a, b in domains]
margin = Fraction(certificate.get("margin", "1/100000"))
assert margin > 0
cores = [
    (math.ceil((a + margin) * grid),
     math.floor((b - margin) * grid))
    for a, b in domains
]
assert certificate["core_interior"] == [list(pair) for pair in cores]
weights = certificate.get("terminal_weights", [10000, 10000, 10000])
assert len(weights) == 3 and all(isinstance(w, int) and w > 0 for w in weights)
assert weights[0] == weights[2] == 10000
assert weights[1] == 10000 * Fraction(certificate.get("middle_weight", "1"))
outer = [(math.floor(a * grid), math.floor(b * grid) + 1) for a, b in domains]
intervals = [tuple(pair) for pair in certificate["accepted_intervals"]]
position = 0
kinds = []
for kind, (left, right) in enumerate(outer):
    cursor = left
    while cursor < right:
        lo, hi = intervals[position]
        assert lo == cursor and lo < hi <= right
        cursor = hi
        position += 1
        kinds.append(kind)
    assert cursor == right
assert position == len(intervals)

translations = [Fraction(0), Fraction(1), ratio, ratio + 1]
offsets = [math.floor(translation * grid) for translation in translations]
error = 3 * (1 + quadratic_coefficient) * grid / (2 * quadratic_coefficient * P)
assert 0 < error < 1
for translation, offset in zip(translations, offsets):
    assert error + translation * grid - offset < 1
outer_right = math.ceil((ratio + 1) * grid / 2) + 2
powers = [beta.numerator ** h for h in range(depth + 1)]
calls = 0

def antichain_numerator(lo, hi, h, needed):
    global calls
    calls += 1
    if lo < 0 or hi > outer_right or lo >= hi:
        return 0
    stop = max(
        (weights[k] * powers[h] if a <= lo and hi <= b else 0)
        for k, (a, b) in enumerate(cores)
    )
    if stop >= needed or h == 0:
        return stop
    children_needed = (needed + beta.denominator - 1) // beta.denominator
    children_sum = 0
    for offset in offsets:
        children_sum += antichain_numerator(
            3 * lo - offset - 1, 3 * hi - offset + 1,
            h - 1, children_needed - children_sum,
        )
        if children_sum >= children_needed:
            break
    return max(stop, beta.denominator * children_sum)

started = time.monotonic()
minimum = None
for index, (lo, hi) in enumerate(intervals):
    target = powers[depth] * (weights[kinds[index]] + 1)
    numerator = antichain_numerator(lo, hi, depth, target)
    assert numerator >= target, (index, lo, hi, numerator, target)
    relative_weight = Fraction(numerator, powers[depth] * weights[kinds[index]])
    minimum = relative_weight if minimum is None else min(minimum, relative_weight)
    if (index + 1) % 5000 == 0:
        print(json.dumps({"verified": index + 1, "calls": calls}), flush=True)

initial = (
    (target_radius_squared - Q**2 - quadratic_coefficient * P**2)
    / (4 * quadratic_coefficient * P)
)
assert any(a <= initial <= b for a, b in domains)
initial_components = [
    kind for kind, (a, b) in enumerate(domains)
    if a + margin < initial < b - margin
]
assert initial_components
result = {
    "status": "PASS",
    "certificate": str(source),
    "certificate_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "beta": str(beta),
    "dimension_lower": math.log(float(beta)) / math.log(3),
    "depth": depth,
    "intervals_verified": len(intervals),
    "calls": calls,
    "minimum_relative_exact_weight": str(minimum),
    "minimum_relative_weight_exceeds": str(1 + Fraction(1, max(weights))),
    "slack_refined_dimension_lower": (
        math.log(float(beta)) + math.log(float(minimum)) / depth
    ) / math.log(3),
    "terminal_integer_weights": weights,
    "source_P": P,
    "source_Q": Q,
    "source_extra_depth": extra_depth,
    "source_level": source_level,
    "physical_a_level": a_level,
    "physical_b_level": b_level,
    "quadratic_coefficient": str(quadratic_coefficient),
    "initial_core_components": initial_components,
    "core_margin": str(margin),
    "initial_state_in_B": True,
    "one_step_error_times_grid": str(error),
    "elapsed_seconds": time.monotonic() - started,
    "scope": "Exact interval return certificate. Nonlinear error bound is audited separately.",
}
Path(args.output).write_text(json.dumps(result, indent=2), encoding="utf-8")
print(json.dumps(result), flush=True)
