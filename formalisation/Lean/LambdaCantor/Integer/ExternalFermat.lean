import LambdaCantor.Integer.Fermat

/-!
# Authorized external theorem: Fermat's Last Theorem

This is explicitly an external axiom, not a claim of a Lean proof of Wiles's
theorem. The user authorized precise established external theorems as black boxes.

Exact mathlib statement: for every natural n >= 3 and nonzero natural a,b,c,
a^n + b^n != c^n. Rational clearing of denominators is proved in mathlib and
used by Integer/Fermat.lean, not added as a second axiom.

Sources (the same bibliography as frozen main.tex, lines 2547–2557):
Andrew Wiles, Modular elliptic curves and Fermat's Last Theorem,
Annals of Mathematics 141 (1995), 443–551.
https://annals.math.princeton.edu/1995/141-3/p01
DOI: 10.2307/2118559.
Richard Taylor and Andrew Wiles, Ring-theoretic properties of certain Hecke
algebras, Annals of Mathematics 141 (1995), 553–572.
https://annals.math.princeton.edu/1995/141-3/p02
DOI: 10.2307/2118560.

Application conditions: exponent n >= 3, both rational physical coordinates
nonzero. Positivity of the chosen Cantor cylinder ensures the latter condition.
No existence, perfectness, slope certificate, or dimension result is assumed.
-/

namespace LambdaCantor.External

axiom wiles_fermat_last_theorem : FermatLastTheorem

end LambdaCantor.External

namespace LambdaCantor.Integer

theorem positive_rational_coordinates_not_on_fermat
    (n : ℕ) (hn : 3 ≤ n) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (rational_x : ∃ q : ℚ, (q : ℝ) = x)
    (rational_y : ∃ q : ℚ, (q : ℝ) = y) : x ^ n + y ^ n ≠ 1 :=
  no_positive_real_rational_fermat External.wiles_fermat_last_theorem
    n hn x y hx hy rational_x rational_y

end LambdaCantor.Integer
