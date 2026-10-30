import Mathlib.NumberTheory.Real.Irrational

noncomputable section
namespace LambdaCantor.Last.ExternalKronecker

/-- Standard forward irrational-rotation density, in integer-lift form.
Source: Milnor, Dynamics lecture notes, Chapter IV, §14C, Lemma 14.14,
https://www.math.stonybrook.edu/~jack/DYNOTES/dn14.pdf .
Every forward tail is an orbit with a different initial point; lifting a
target arc gives the integer `second` below. This is independent of Cantor
sets, Fermat curves, or any theorem of the manuscript.
Registered in EXTERNAL_THEOREMS-R025-LastAE.md.
-/
axiom forward_integer_difference_approximation {exponent : ℝ}
    (irrational : Irrational exponent) (target : ℝ) {epsilon : ℝ}
    (epsilon_positive : 0 < epsilon) (start : ℕ) :
    ∃ first : ℕ, start ≤ first ∧ ∃ second : ℤ,
      |(second : ℝ) - exponent * first - target| < epsilon

end LambdaCantor.Last.ExternalKronecker
