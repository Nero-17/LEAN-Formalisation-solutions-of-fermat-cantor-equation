import LambdaCantor.Circle.ZeroIntervals

noncomputable section
namespace LambdaCantor.Circle

theorem circle_shell_relative_depth (ratio outerX outerY : ℝ) (horizontalDepth verticalDepth : ℕ)
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (x_lower : 1 - ratio ≤ outerX) (x_upper : outerX ≤ 1)
    (y_lower : 1 - ratio ≤ outerY) (y_upper : outerY ≤ 1)
    (deficit_upper : ratio ^ verticalDepth * outerY ≤ ratio)
    (equation : ratio ^ (2 * horizontalDepth) * outerX ^ 2 =
      ratio ^ verticalDepth * outerY * (2 - ratio ^ verticalDepth * outerY)) :
    verticalDepth = 2 * horizontalDepth + 1 := by
  have positive : 0 < ratio := by linarith
  have small : ratio < (1 / 3 : ℝ) := by linarith
  have less_one : ratio < 1 := by linarith
  have x_nonnegative : 0 ≤ outerX := by linarith
  have y_positive : 0 < outerY := by linarith
  have deficit_nonnegative : 0 ≤ ratio ^ verticalDepth * outerY := by positivity
  have after : 2 * horizontalDepth < verticalDepth := by
    by_contra contrary
    have power_order := power_antitone positive.le less_one.le (le_of_not_gt contrary)
    have left_upper : ratio ^ (2 * horizontalDepth) * outerX ^ 2 ≤ ratio ^ verticalDepth := by
      calc
        _ ≤ ratio ^ (2 * horizontalDepth) * 1 := by gcongr; nlinarith
        _ ≤ ratio ^ verticalDepth := by simpa using power_order
    have right_factor : 1 < outerY * (2 - ratio ^ verticalDepth * outerY) := by
      have minimum : (1 - ratio) * (2 - ratio) ≤
          outerY * (2 - ratio ^ verticalDepth * outerY) := by gcongr <;> linarith
      nlinarith [sq_nonneg ratio]
    have right_lower : ratio ^ verticalDepth <
        ratio ^ verticalDepth * outerY * (2 - ratio ^ verticalDepth * outerY) := by
      nlinarith [mul_pos (pow_pos positive verticalDepth) (sub_pos.mpr right_factor)]
    linarith
  have before : verticalDepth < 2 * horizontalDepth + 2 := by
    by_contra contrary
    have power_order := power_antitone positive.le less_one.le (le_of_not_gt contrary)
    rw [pow_add] at power_order
    have right_upper : ratio ^ verticalDepth * outerY * (2 - ratio ^ verticalDepth * outerY) ≤
        2 * ratio ^ verticalDepth := by
      calc
        _ ≤ ratio ^ verticalDepth * 1 * 2 := by gcongr <;> linarith
        _ = 2 * ratio ^ verticalDepth := by ring
    have square_lower : (1 - ratio) ^ 2 ≤ outerX ^ 2 := by nlinarith
    have left_lower := mul_le_mul_of_nonneg_left square_lower (pow_nonneg positive.le (2 * horizontalDepth))
    have quadratic_gap : 0 < (1 - ratio) ^ 2 - 2 * ratio ^ 2 := by
      nlinarith [mul_pos positive (sub_pos.mpr small)]
    have strict_gap := mul_pos (pow_pos positive (2 * horizontalDepth)) quadratic_gap
    nlinarith
  omega

theorem no_nonaxis_ordered_zero_window {ratio x y : ℝ} (depth : ℕ)
    (depth_at_least_three : 3 ≤ depth)
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (x_mem : x ∈ cantorSet ratio) (y_mem : y ∈ cantorSet ratio)
    (y_right : 1 - ratio ≤ y) (x_nonzero : x ≠ 0) (y_not_one : y ≠ 1)
    (level_lower : (379 / 100 : ℝ) * ratio ^ (2 * depth + 2) < 4 * ratio - 1 - ratio ^ 2)
    (level_upper : 4 * ratio - 1 - ratio ^ 2 < (381 / 100 : ℝ) * ratio ^ (2 * depth + 2)) :
    x ^ 2 + y ^ 2 ≠ 1 := by
  have positive : 0 < ratio := by linarith
  have less_one : ratio < 1 := by linarith
  obtain ⟨horizontalDepth, outerX, outerX_mem, outerX_lower, outerX_upper, x_shell⟩ :=
    exists_near_axis_shell positive less_one x_mem x_nonzero
  obtain ⟨verticalDepth, outerY, outerY_mem, outerY_lower, outerY_upper, y_shell⟩ :=
    exists_near_axis_shell positive less_one
      (one_sub_mem_cantorSet positive.le less_one y_mem) (sub_ne_zero.mpr (Ne.symm y_not_one))
  have deficit_upper : ratio ^ verticalDepth * outerY ≤ ratio := by linarith
  have power_squared : ratio ^ (2 * horizontalDepth) = (ratio ^ horizontalDepth) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm horizontalDepth 2]
  intro equation
  have y_value : y = 1 - ratio ^ verticalDepth * outerY := by linarith
  rw [x_shell, y_value] at equation
  have normalized : ratio ^ (2 * horizontalDepth) * outerX ^ 2 =
      ratio ^ verticalDepth * outerY * (2 - ratio ^ verticalDepth * outerY) := by
    rw [power_squared]
    nlinarith
  have depth_relation := circle_shell_relative_depth ratio outerX outerY horizontalDepth verticalDepth
    lower upper outerX_lower outerX_upper outerY_lower outerY_upper deficit_upper normalized
  rw [depth_relation, pow_add, pow_one] at normalized
  have product_zero : ratio ^ (2 * horizontalDepth) *
      (outerX ^ 2 - 2 * ratio * outerY + ratio ^ (2 * horizontalDepth + 2) * outerY ^ 2) = 0 := by
    rw [pow_add]
    nlinarith
  have outer_equation := (mul_eq_zero.mp product_zero).resolve_left (ne_of_gt (pow_pos positive _))
  exact zero_window_outer_equation_impossible ratio outerX outerY depth horizontalDepth
    depth_at_least_three lower upper outerX_mem outerY_mem outerX_lower level_lower level_upper outer_equation

/-- Pointwise zero-interval theorem in the exact open polynomial window.
It includes genuine Cantor membership, all scales, and both axis exceptions. -/
theorem circle_axis_only_in_zero_window {ratio x y : ℝ} (depth : ℕ)
    (depth_at_least_three : 3 ≤ depth)
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (level_lower : (379 / 100 : ℝ) * ratio ^ (2 * depth + 2) < 4 * ratio - 1 - ratio ^ 2)
    (level_upper : 4 * ratio - 1 - ratio ^ 2 < (381 / 100 : ℝ) * ratio ^ (2 * depth + 2))
    (x_mem : x ∈ cantorSet ratio) (y_mem : y ∈ cantorSet ratio)
    (equation : x ^ 2 + y ^ 2 = 1) : (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  have positive : 0 < ratio := by linarith
  have small : ratio < (1 / 3 : ℝ) := by linarith
  have less_one : ratio < 1 := by linarith
  have x_bounds := cantorSet_subset_unitInterval positive.le less_one x_mem
  have y_bounds := cantorSet_subset_unitInterval positive.le less_one y_mem
  by_cases x_zero : x = 0
  · exact Or.inl ⟨x_zero, by nlinarith [y_bounds.1]⟩
  by_cases y_zero : y = 0
  · exact Or.inr ⟨by nlinarith [x_bounds.1], y_zero⟩
  have x_not_one : x ≠ 1 := by intro one; apply y_zero; nlinarith [y_bounds.1]
  have y_not_one : y ≠ 1 := by intro one; apply x_zero; nlinarith [x_bounds.1]
  rcases cantor_first_level_bounds positive.le less_one x_mem with x_left | x_right <;>
    rcases cantor_first_level_bounds positive.le less_one y_mem with y_left | y_right
  · have x_square : x ^ 2 ≤ ratio ^ 2 := by nlinarith [x_bounds.1]
    have y_square : y ^ 2 ≤ ratio ^ 2 := by nlinarith [y_bounds.1]
    nlinarith [mul_pos positive (sub_pos.mpr small)]
  · exact False.elim (no_nonaxis_ordered_zero_window depth depth_at_least_three lower upper x_mem y_mem
      y_right x_zero y_not_one level_lower level_upper equation)
  · exact False.elim (no_nonaxis_ordered_zero_window depth depth_at_least_three lower upper y_mem x_mem
      x_right y_zero x_not_one level_lower level_upper (by nlinarith))
  · have x_square : (1 - ratio) ^ 2 ≤ x ^ 2 := by nlinarith [x_bounds.1]
    have y_square : (1 - ratio) ^ 2 ≤ y ^ 2 := by nlinarith [y_bounds.1]
    have gap := projection_gap_certificate ratio lower upper
    nlinarith

end LambdaCantor.Circle
