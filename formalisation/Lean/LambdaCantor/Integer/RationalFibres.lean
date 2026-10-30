import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace LambdaCantor.Integer

/-- Two distinct rational points cannot lie in one affine fibre of an
irrational slope. The irrationality hypothesis is stated without any
auxiliary choice of rational coordinates. -/
theorem rational_points_unique_in_irrational_fibre (r : ℝ)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ))
    (x₁ y₁ x₂ y₂ : ℚ)
    (level : r * x₁ + y₁ = r * x₂ + y₂) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hx : x₁ = x₂ := by
    by_contra hne
    have hden : (x₁ : ℝ) - x₂ ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr hne)
    apply irrational ((y₂-y₁)/(x₁-x₂))
    push_cast
    apply (eq_div_iff hden).mpr
    nlinarith [level]
  refine ⟨hx, ?_⟩
  subst x₂
  have hy : (y₁ : ℝ) = y₂ := by linarith [level]
  exact_mod_cast hy

end LambdaCantor.Integer
