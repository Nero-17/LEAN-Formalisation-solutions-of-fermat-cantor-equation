import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace LambdaCantor.Integer

/-- Rational clearing of denominators is already proved in mathlib's FLT API.
The only external hypothesis here is precisely Fermat's Last Theorem.
Source: Wiles, Annals of Mathematics 141 (1995), 443–551, together with
Taylor–Wiles, ibid. 553–572. This file does not declare that result as an axiom. -/
theorem no_nonzero_rational_fermat (fermat : FermatLastTheorem)
    (n : ℕ) (hn : 3 ≤ n) (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ n + y ^ n ≠ 1 := by
  have h := (fermatLastTheoremFor_iff_rat.mp (fermat n hn)) x y 1 hx hy one_ne_zero
  simpa using h

theorem no_positive_real_rational_fermat (fermat : FermatLastTheorem)
    (n : ℕ) (hn : 3 ≤ n) (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (rational_x : ∃ q : ℚ, (q : ℝ) = x)
    (rational_y : ∃ q : ℚ, (q : ℝ) = y) : x ^ n + y ^ n ≠ 1 := by
  obtain ⟨a, rfl⟩ := rational_x
  obtain ⟨b, rfl⟩ := rational_y
  intro h
  apply no_nonzero_rational_fermat fermat n hn a b
  · intro ha; simp [ha] at hx
  · intro hb; simp [hb] at hy
  · exact_mod_cast h

end LambdaCantor.Integer
