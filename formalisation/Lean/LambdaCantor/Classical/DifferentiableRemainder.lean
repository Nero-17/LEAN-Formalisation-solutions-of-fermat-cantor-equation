import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.Classical

theorem differentiable_remainder_bound
    (function : ℝ × ℝ → ℝ) (derivative : (ℝ × ℝ) →L[ℝ] ℝ) (point : ℝ × ℝ)
    (differentiable : HasFDerivAt function derivative point)
    (error : ℝ) (positive : 0 < error) :
    ∃ radius > 0, ∀ displacement : ℝ × ℝ, ‖displacement‖ < radius →
      ‖function (point + displacement) - function point - derivative displacement‖ ≤
        error * ‖displacement‖ := by
  have estimate := (hasFDerivAt_iff_isLittleO_nhds_zero.mp differentiable).bound positive
  obtain ⟨radius, radius_positive, contained⟩ := Metric.mem_nhds_iff.mp estimate
  refine ⟨radius, radius_positive, fun displacement small => ?_⟩
  apply contained
  simpa only [Metric.mem_ball, dist_zero_right] using small

/-- Differentiability controls the normalized remainder uniformly over the whole
unit ball of directions, even when the direction changes with the scale. -/
theorem differentiable_uniform_scaled_remainder
    (function : ℝ × ℝ → ℝ) (derivative : (ℝ × ℝ) →L[ℝ] ℝ) (point : ℝ × ℝ)
    (differentiable : HasFDerivAt function derivative point)
    (error : ℝ) (positive : 0 < error) :
    ∃ radius > 0, ∀ side : ℝ, 0 < side → side < radius →
      ∀ direction : ℝ × ℝ, ‖direction‖ ≤ 1 →
        ‖function (point + side • direction) - function point -
          derivative (side • direction)‖ / side ≤ error := by
  obtain ⟨radius, radius_positive, estimate⟩ :=
    differentiable_remainder_bound function derivative point differentiable error positive
  refine ⟨radius, radius_positive, fun side side_positive side_small direction unit => ?_⟩
  have size : ‖side • direction‖ ≤ side := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos side_positive]
    nlinarith
  have bound := estimate (side • direction) (lt_of_le_of_lt size side_small)
  apply (div_le_iff₀ side_positive).mpr
  nlinarith

end LambdaCantor.Classical
