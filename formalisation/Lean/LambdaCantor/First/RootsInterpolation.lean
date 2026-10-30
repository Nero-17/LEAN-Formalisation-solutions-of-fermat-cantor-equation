import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.First.Roots

/-- Exact frequency-balancing identity in the Fourier interpolation step. -/
theorem fourier_balance (displacement order : ℝ) (displacement_pos : 0 < displacement)
    (order_pos : 0 < order) :
    displacement ^ (2 : ℝ) *
        (displacement ^ (-2 / (3 + 2 * order))) ^ (3 : ℝ) +
      (displacement ^ (-2 / (3 + 2 * order))) ^ (-2 * order) =
    2 * displacement ^ (4 * order / (3 + 2 * order)) := by
  have denominator_ne : 3 + 2 * order ≠ 0 := by linarith
  have low_exponent : (2 : ℝ) + (-2 / (3 + 2 * order)) * 3 =
      4 * order / (3 + 2 * order) := by field_simp; ring
  have high_exponent : (-2 / (3 + 2 * order)) * (-2 * order) =
      4 * order / (3 + 2 * order) := by ring
  rw [← Real.rpow_mul displacement_pos.le, ← Real.rpow_add displacement_pos,
    low_exponent, ← Real.rpow_mul displacement_pos.le, high_exponent]
  ring

/-- Optimization of the low/high-frequency squared error estimate. The analytic
Fourier bounds remain explicit hypotheses; no regularity conclusion is assumed. -/
theorem fourier_interpolation_rate (error constant displacement order : ℝ)
    (constant_nonnegative : 0 ≤ constant) (displacement_pos : 0 < displacement)
    (order_pos : 0 < order)
    (split_bound : ∀ radius : ℝ, 0 < radius →
      error ^ 2 ≤ constant * (displacement ^ (2 : ℝ) * radius ^ (3 : ℝ) +
        radius ^ (-2 * order))) :
    error ≤ Real.sqrt (2 * constant) *
      displacement ^ (2 * order / (3 + 2 * order)) := by
  have bound := split_bound (displacement ^ (-2 / (3 + 2 * order)))
    (Real.rpow_pos_of_pos displacement_pos _)
  rw [fourier_balance displacement order displacement_pos order_pos] at bound
  have power_square :
      (displacement ^ (2 * order / (3 + 2 * order))) ^ (2 : ℕ) =
        displacement ^ (4 * order / (3 + 2 * order)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul displacement_pos.le]
    congr 1
    ring
  have square_root : (Real.sqrt (2 * constant)) ^ 2 = 2 * constant :=
    Real.sq_sqrt (by positivity)
  have power_pos := Real.rpow_pos_of_pos displacement_pos
    (2 * order / (3 + 2 * order))
  have root_nonnegative := Real.sqrt_nonneg (2 * constant)
  have square_product :
      (Real.sqrt (2 * constant) * displacement ^ (2 * order / (3 + 2 * order))) ^ 2 =
      2 * constant * displacement ^ (4 * order / (3 + 2 * order)) := by
    rw [mul_pow, square_root, power_square]
  have product_nonnegative : 0 ≤ Real.sqrt (2 * constant) *
      displacement ^ (2 * order / (3 + 2 * order)) := mul_nonneg root_nonnegative power_pos.le
  nlinarith

/-- The normalized parent-child replacement rate is summable. The interpolation
exponent is at most one, so a linear polynomial majorant suffices. -/
theorem summable_replacement_rate (ratio exponent : ℝ)
    (ratio_nonnegative : 0 ≤ ratio) (ratio_lt_one : ratio < 1)
    (exponent_pos : 0 < exponent) (exponent_le_one : exponent ≤ 1) :
    Summable (fun depth : ℕ => ((depth : ℝ) + 1) ^ exponent *
      ratio ^ (exponent * (depth : ℝ))) := by
  have contracted_nonnegative : 0 ≤ ratio ^ exponent := Real.rpow_nonneg ratio_nonnegative _
  have contracted_lt_one : ratio ^ exponent < 1 :=
    Real.rpow_lt_one ratio_nonnegative ratio_lt_one exponent_pos
  have contracted_norm : ‖ratio ^ exponent‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg contracted_nonnegative] using contracted_lt_one
  have linear_summable := summable_pow_mul_geometric_of_norm_lt_one 1 contracted_norm
  have constant_summable := summable_geometric_of_lt_one contracted_nonnegative contracted_lt_one
  have majorant : Summable (fun depth : ℕ => ((depth : ℝ) + 1) *
      (ratio ^ exponent) ^ depth) := by
    simpa only [pow_one, add_mul, one_mul] using linear_summable.add constant_summable
  apply Summable.of_nonneg_of_le (fun depth => by positivity) _ majorant
  intro depth
  rw [Real.rpow_mul ratio_nonnegative, Real.rpow_natCast]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg contracted_nonnegative _)
  apply Real.rpow_le_self_of_one_le _ exponent_le_one
  linarith [Nat.cast_nonneg (α := ℝ) depth]

/-- The exponent produced by frequency splitting lies in the range required for
the summability argument. -/
theorem interpolation_exponent_bounds (order : ℝ) (order_pos : 0 < order) :
    0 < 2 * order / (3 + 2 * order) ∧ 2 * order / (3 + 2 * order) ≤ 1 := by
  have denominator_pos : 0 < 3 + 2 * order := by linarith
  constructor
  · positivity
  · apply (div_le_iff₀ denominator_pos).2
    linarith

end LambdaCantor.First.Roots
