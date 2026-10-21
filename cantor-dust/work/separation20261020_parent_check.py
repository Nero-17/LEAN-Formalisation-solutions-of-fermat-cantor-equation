"""Independent fixed-depth coverage and endpoint sign reconstruction."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json

certificate = json.loads(Path("work/separation20261020_low_certificate.json").read_text())
contraction = Fraction(131, 500)

def cylinder(word):
    left, length = Fraction(0), Fraction(1)
    for digit in word:
        if digit == "1":
            left += length * (1 - contraction)
        length *= contraction
    return left, left + length

minimum_margin = Fraction(1)
for row in certificate["leaves"]:
    lower_x, upper_x = cylinder(row["x_word"])
    lower_y, upper_y = cylinder(row["y_word"])
    if row["sign"] == "+":
        margin = lower_x**4 - 4 * contraction * upper_y
    else:
        # Direct binomial expression, rather than the expanded certificate.
        margin = contraction * (1 - (1 - contraction**5 * lower_y)**4) / contraction**5 - upper_x**4
    assert margin > 0
    assert margin == Fraction(row["margin_exact"])
    minimum_margin = min(minimum_margin, margin)

words = ["1" + "".join(tail) for tail in product("01", repeat=4)]
for x_word, y_word in product(words, repeat=2):
    covering = [row for row in certificate["leaves"]
                if x_word.startswith(row["x_word"]) and y_word.startswith(row["y_word"])]
    assert len(covering) == 1

assert 2 * contraction**4 < 1
assert 4 * (1 - contraction)**4 > 1
assert 4 * contraction**2 < (1 - contraction)**4
assert 2 * (1 - contraction + contraction**2)**4 < 1
assert (1 - contraction)**4 + (1 - contraction**2)**4 > 1

print("PASS: 256 depth-five rectangles covered exactly once; all 19 signs and 5 geometric conditions exact.")
print("Minimum leaf margin:", minimum_margin)
