import LambdaCantor.Circle.Cylinders
import LambdaCantor.Circle.ZeroIntervalAlgebra

noncomputable section
namespace LambdaCantor.Circle

theorem horizontal_cylinder_threshold (ratio tailScale outerX outerY : ℝ)
    (positive : 0 < ratio) (less_one : ratio < 1)
    (tail_positive : 0 < tailScale)
    (outer_square : 1 < 2 * (1 - ratio) ^ 2)
    (residual_small : 4 * ratio - 1 - ratio ^ 2 < tailScale)
    (outer_lower : 1 - ratio ≤ outerX) (outerY_upper : outerY ≤ 1)
    (equation_bound : outerX ^ 2 ≤ 2 * ratio * outerY) :
    outerX < (1 - ratio) * (1 + tailScale) := by
  by_contra contrary
  have threshold_le : (1 - ratio) * (1 + tailScale) ≤ outerX := le_of_not_gt contrary
  have threshold_positive : 0 < (1 - ratio) * (1 + tailScale) := by positivity
  have square_difference := mul_nonneg (sub_nonneg.mpr threshold_le)
    (show 0 ≤ outerX + (1 - ratio) * (1 + tailScale) by linarith)
  have strict_increase := mul_pos tail_positive (sub_pos.mpr outer_square)
  have nonnegative_remainder := sq_nonneg ((1 - ratio) * tailScale)
  have upper : outerX ^ 2 ≤ 2 * ratio := by nlinarith [mul_nonneg positive.le (sub_nonneg.mpr outerY_upper)]
  nlinarith

theorem vertical_cylinder_threshold (ratio tailScale outerX outerY : ℝ)
    (positive : 0 < ratio) (less_half : ratio < 1 / 2)
    (tail_positive : 0 < tailScale)
    (residual_small : 4 * ratio - 1 - ratio ^ 2 < ratio * tailScale)
    (outer_lower : 1 - ratio ≤ outerX)
    (equation_bound : outerX ^ 2 ≤ 2 * ratio * outerY) :
    1 - outerY < (1 - ratio) * tailScale := by
  have square_difference := mul_nonneg (sub_nonneg.mpr outer_lower)
    (show 0 ≤ outerX + (1 - ratio) by linarith)
  have multiplied : ratio * (2 * (1 - outerY)) < ratio * tailScale := by nlinarith
  have deficit_bound := (mul_lt_mul_iff_of_pos_left positive).mp multiplied
  have strict_margin := mul_pos tail_positive (show 0 < 2 * (1 - ratio) - 1 by linarith)
  nlinarith

/-- The finer cylinders in the zero-interval proof are forced by the actual
Cantor gap structure and the scalar circle equation. -/
theorem forced_cantor_cylinders {ratio outerX outerY : ℝ} (depth : ℕ)
    (depth_positive : 0 < depth)
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (x_mem : outerX ∈ cantorSet ratio) (y_mem : outerY ∈ cantorSet ratio)
    (x_outer : 1 - ratio ≤ outerX)
    (residual_small : 4 * ratio - 1 - ratio ^ 2 < ratio ^ (2 * depth))
    (equation_bound : outerX ^ 2 ≤ 2 * ratio * outerY) :
    ∃ firstTail ∈ cantorSet ratio, ∃ secondTail ∈ cantorSet ratio,
      outerX = 1 - ratio + ratio ^ (2 * depth + 1) * firstTail ∧
      outerY = 1 - ratio ^ (2 * depth) * secondTail := by
  have positive : 0 < ratio := by linarith
  have less_half : ratio < 1 / 2 := by linarith
  have less_one : ratio < 1 := by linarith
  have y_bounds := cantorSet_subset_unitInterval positive.le less_one y_mem
  have first_gap := projection_gap_certificate ratio lower upper
  have outer_square : 1 < 2 * (1 - ratio) ^ 2 := by nlinarith
  have horizontal_bound := horizontal_cylinder_threshold ratio (ratio ^ (2 * depth)) outerX outerY
    positive less_one (pow_pos positive _) outer_square residual_small x_outer y_bounds.2 equation_bound
  obtain ⟨initialTail, initial_mem, initial_equation⟩ := exists_outer_right_tail positive less_half x_mem x_outer
  have power_step : ratio ^ (2 * depth) = ratio * ratio ^ (2 * depth - 1) := by
    have exponent : 2 * depth = (2 * depth - 1) + 1 := by omega
    conv_lhs => rw [exponent, pow_succ']
  have initial_small : initialTail < (1 - ratio) * ratio ^ (2 * depth - 1) := by
    apply (mul_lt_mul_iff_of_pos_left positive).mp
    rw [power_step] at horizontal_bound
    nlinarith
  obtain ⟨firstTail, first_mem, first_equation⟩ := exists_leftmost_cylinder positive less_one initial_mem
    (2 * depth) (by omega) initial_small
  have vertical_bound := vertical_cylinder_threshold ratio (ratio ^ (2 * depth - 1)) outerX outerY
    positive less_half (pow_pos positive _)
    (by simpa only [power_step] using residual_small) x_outer equation_bound
  obtain ⟨secondTail, second_mem, second_equation⟩ := exists_rightmost_cylinder positive less_one y_mem
    (2 * depth) (by omega) vertical_bound
  refine ⟨firstTail, first_mem, secondTail, second_mem, ?_, second_equation⟩
  rw [initial_equation, first_equation, pow_succ]
  ring

end LambdaCantor.Circle
