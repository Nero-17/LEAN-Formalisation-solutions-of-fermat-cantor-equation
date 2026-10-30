import LambdaCantor.Circle.ForcedCylinders
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.Circle

theorem zero_interval_residual_small (ratio : ℝ) (depth : ℕ)
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (level_upper : 4 * ratio - 1 - ratio ^ 2 < (381 / 100 : ℝ) * ratio ^ (2 * depth + 2)) :
    4 * ratio - 1 - ratio ^ 2 < ratio ^ (2 * depth) := by
  have positive : 0 < ratio := by linarith
  have scale_bound := earlier_scale_certificate ratio lower upper
  have strict_margin := mul_pos (pow_pos positive (2 * depth))
    (show 0 < 1 - (381 / 100 : ℝ) * ratio ^ 2 by linarith)
  rw [pow_add] at level_upper
  nlinarith

theorem outer_equation_minimum (ratio outerX outerY coefficient : ℝ)
    (positive : 0 < ratio) (less_one : ratio < 1)
    (x_lower : 1 - ratio ≤ outerX)
    (y_nonnegative : 0 ≤ outerY) (y_upper : outerY ≤ 1)
    (coefficient_nonnegative : 0 ≤ coefficient) (coefficient_upper : coefficient ≤ ratio)
    (equation : outerX ^ 2 - 2 * ratio * outerY + coefficient * outerY ^ 2 = 0) :
    coefficient ≤ 4 * ratio - 1 - ratio ^ 2 := by
  have square_difference := mul_nonneg (sub_nonneg.mpr x_lower)
    (show 0 ≤ outerX + (1 - ratio) by linarith)
  have coefficient_bound : coefficient * (1 + outerY) ≤ 2 * ratio := by
    have : coefficient * (1 + outerY) ≤ coefficient * 2 := by nlinarith
    linarith
  have monotonicity := mul_nonneg (sub_nonneg.mpr y_upper) (sub_nonneg.mpr coefficient_bound)
  nlinarith

/-- Once the relative vertical depth is `2*k+1`, every scale is excluded on
the stated open level window. This discharges the earlier-scale reduction,
the finer-cylinder forcing, and both projection gaps. -/
theorem zero_window_outer_equation_impossible (ratio outerX outerY : ℝ) (depth scale : ℕ)
    (depth_at_least_three : 3 ≤ depth)
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (x_mem : outerX ∈ cantorSet ratio) (y_mem : outerY ∈ cantorSet ratio)
    (x_lower : 1 - ratio ≤ outerX)
    (level_lower : (379 / 100 : ℝ) * ratio ^ (2 * depth + 2) < 4 * ratio - 1 - ratio ^ 2)
    (level_upper : 4 * ratio - 1 - ratio ^ 2 < (381 / 100 : ℝ) * ratio ^ (2 * depth + 2)) :
    outerX ^ 2 - 2 * ratio * outerY + ratio ^ (2 * scale + 2) * outerY ^ 2 ≠ 0 := by
  have positive : 0 < ratio := by linarith
  have less_one : ratio < 1 := by linarith
  have y_bounds := cantorSet_subset_unitInterval positive.le less_one y_mem
  have residual_small := zero_interval_residual_small ratio depth lower upper level_upper
  intro equation
  have coefficient_upper : ratio ^ (2 * scale + 2) ≤ ratio := by
    simpa using power_antitone positive.le less_one.le (show 1 ≤ 2 * scale + 2 by omega)
  have minimum := outer_equation_minimum ratio outerX outerY (ratio ^ (2 * scale + 2))
    positive less_one x_lower y_bounds.1 y_bounds.2 (pow_nonneg positive.le _) coefficient_upper equation
  have scale_at_least_depth : depth ≤ scale := by
    by_contra earlier
    have power_bound := power_antitone positive.le less_one.le
      (show 2 * scale + 2 ≤ 2 * depth by omega)
    linarith
  have equation_bound : outerX ^ 2 ≤ 2 * ratio * outerY := by
    nlinarith [mul_nonneg (pow_nonneg positive.le (2 * scale + 2)) (sq_nonneg outerY)]
  obtain ⟨firstTail, first_mem, secondTail, second_mem, first_equation, second_equation⟩ :=
    forced_cantor_cylinders depth (by omega) lower upper x_mem y_mem x_lower residual_small equation_bound
  let level : ℝ := (4 * ratio - 1 - ratio ^ 2) / ratio ^ (2 * depth + 2)
  have level_positive_denominator : 0 < ratio ^ (2 * depth + 2) := pow_pos positive _
  have normalized_lower : (379 / 100 : ℝ) < level := by
    exact (lt_div_iff₀ level_positive_denominator).mpr level_lower
  have normalized_upper : level < (381 / 100 : ℝ) := by
    exact (div_lt_iff₀ level_positive_denominator).mpr level_upper
  have level_equation : ratio ^ 2 * ratio ^ (2 * depth) * level = 4 * ratio - 1 - ratio ^ 2 := by
    have power_identity : ratio ^ 2 * ratio ^ (2 * depth) = ratio ^ (2 * depth + 2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [power_identity]
    dsimp [level]
    field_simp [ne_of_gt positive]
  have coefficient_identity : ratio ^ (2 * scale + 2) =
      ratio ^ 2 * ratio ^ (2 * depth) * ratio ^ (2 * (scale - depth)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have first_power : ratio ^ (2 * depth + 1) = ratio * ratio ^ (2 * depth) := by rw [pow_succ']
  rw [first_equation, second_equation, first_power, coefficient_identity] at equation
  have residual_identity := forced_cylinder_residual ratio (ratio ^ (2 * depth))
    (ratio ^ (2 * (scale - depth))) firstTail secondTail level level_equation
  have product_zero : ratio * ratio ^ (2 * depth) *
      (2 * ((1 - ratio) * firstTail + secondTail) +
        ratio * ratio ^ (2 * depth) * firstTail ^ 2 +
        ratio * ratio ^ (2 * (scale - depth)) * (1 - ratio ^ (2 * depth) * secondTail) ^ 2 - ratio * level) = 0 := by
    nlinarith [residual_identity]
  have normalized_equation : ratio * level = 2 * ((1 - ratio) * firstTail + secondTail) +
      ratio * ratio ^ (2 * depth) * firstTail ^ 2 +
      ratio * ratio ^ (2 * (scale - depth)) * (1 - ratio ^ (2 * depth) * secondTail) ^ 2 := by
    have vanishing := (mul_eq_zero.mp product_zero).resolve_left (ne_of_gt (mul_pos positive (pow_pos positive _)))
    linarith
  apply forced_cylinders_exclude_solution ratio (ratio ^ (2 * depth))
    (ratio ^ (2 * (scale - depth))) firstTail secondTail level lower upper
    (pow_nonneg positive.le _) (power_antitone positive.le less_one.le (by omega))
    (pow_nonneg positive.le _) _ first_mem second_mem normalized_lower normalized_upper normalized_equation
  by_cases equal : scale = depth
  · left
    simp [equal]
  · right
    exact power_antitone positive.le less_one.le (by omega)

end LambdaCantor.Circle
