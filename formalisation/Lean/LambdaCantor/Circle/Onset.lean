import LambdaCantor.Circle.OnsetAlgebra
import LambdaCantor.SelfSimilarity

noncomputable section
namespace LambdaCantor.Circle

theorem cantor_first_level_bounds {ratio coordinate : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (membership : coordinate ∈ cantorSet ratio) :
    coordinate ≤ ratio ∨ 1 - ratio ≤ coordinate := by
  rcases membership with ⟨digits, rfl⟩
  have bounds := cantorSet_subset_unitInterval nonnegative less_one
    (show address ratio (fun j => digits (j + 1)) ∈ cantorSet ratio from ⟨_, rfl⟩)
  rw [address_first_digit nonnegative less_one]
  cases digit : digits 0 <;> simp only [digit, Bool.false_eq_true, if_false, if_true,
    mul_zero, mul_one, zero_add]
  · left
    nlinarith [bounds.2]
  · right
    nlinarith [bounds.1]

theorem power_antitone {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (at_most_one : ratio ≤ 1) {earlier later : ℕ} (ordered : earlier ≤ later) :
    ratio ^ later ≤ ratio ^ earlier := by
  obtain ⟨difference, rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [pow_add]
  exact mul_le_of_le_one_right (pow_nonneg nonnegative _)
    (pow_le_one₀ nonnegative at_most_one)

/-- Genuine Cantor membership is used to obtain the discrete near-axis shells;
the two possible relative depths are then excluded by exact inequalities. -/
theorem no_nonaxis_ordered {ratio x y : ℝ} (positive : 0 < ratio)
    (below_onset : ratio ≤ onset)
    (x_membership : x ∈ cantorSet ratio) (y_membership : y ∈ cantorSet ratio)
    (x_left : x ≤ ratio) (y_right : 1 - ratio ≤ y)
    (x_nonzero : x ≠ 0) (y_not_one : y ≠ 1) : x ^ 2 + y ^ 2 ≠ 1 := by
  have small : ratio < (1 / 3 : ℝ) := lt_of_le_of_lt below_onset onset_lt_one_third
  have less_one : ratio < 1 := by linarith
  have x_bounds := cantorSet_subset_unitInterval positive.le less_one x_membership
  have y_bounds := cantorSet_subset_unitInterval positive.le less_one y_membership
  obtain ⟨horizontalDepth, outerX, outerX_mem, outerX_lower, outerX_upper, x_shell⟩ :=
    exists_near_axis_shell positive less_one x_membership x_nonzero
  obtain ⟨verticalDepth, outerY, outerY_mem, outerY_lower, outerY_upper, y_shell⟩ :=
    exists_near_axis_shell positive less_one
      (one_sub_mem_cantorSet positive.le less_one y_membership)
      (sub_ne_zero.mpr (Ne.symm y_not_one))
  have outerX_nonnegative : 0 ≤ outerX := by linarith
  have outerY_positive : 0 < outerY := by linarith
  have deficit_positive : 0 < ratio ^ verticalDepth * outerY :=
    mul_pos (pow_pos positive _) outerY_positive
  have deficit_le : ratio ^ verticalDepth * outerY ≤ ratio := by linarith
  have power_squared : ratio ^ (2 * horizontalDepth) = (ratio ^ horizontalDepth) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm horizontalDepth 2]
  intro equation
  have y_value : y = 1 - ratio ^ verticalDepth * outerY := by linarith
  rw [x_shell, y_value] at equation
  have normalized : ratio ^ (2 * horizontalDepth) * outerX ^ 2 =
      ratio ^ verticalDepth * outerY * (2 - ratio ^ verticalDepth * outerY) := by
    rw [power_squared]
    nlinarith [equation]
  by_cases depths : verticalDepth ≤ 2 * horizontalDepth
  · have power_order := power_antitone positive.le less_one.le depths
    have left_upper : ratio ^ (2 * horizontalDepth) * outerX ^ 2 ≤ ratio ^ verticalDepth := by
      calc
        _ ≤ ratio ^ (2 * horizontalDepth) * 1 := by gcongr; nlinarith
        _ ≤ ratio ^ verticalDepth := by simpa using power_order
    have right_factor : 1 < outerY * (2 - ratio ^ verticalDepth * outerY) := by
      have lower : (1 - ratio) * (2 - ratio) ≤
          outerY * (2 - ratio ^ verticalDepth * outerY) := by gcongr <;> linarith
      nlinarith [sq_nonneg ratio]
    have right_lower : ratio ^ verticalDepth <
        ratio ^ verticalDepth * outerY * (2 - ratio ^ verticalDepth * outerY) := by
      nlinarith [mul_pos (pow_pos positive verticalDepth) (sub_pos.mpr right_factor)]
    linarith
  · have power_order := power_antitone positive.le less_one.le
      (show 2 * horizontalDepth + 1 ≤ verticalDepth by omega)
    rw [pow_succ] at power_order
    have right_upper : ratio ^ verticalDepth * outerY * (2 - ratio ^ verticalDepth * outerY) ≤
        (ratio ^ (2 * horizontalDepth) * ratio) * (2 - ratio ^ verticalDepth * outerY) := by
      calc
        _ ≤ ratio ^ verticalDepth * 1 * (2 - ratio ^ verticalDepth * outerY) := by gcongr <;> linarith
        _ ≤ (ratio ^ (2 * horizontalDepth) * ratio) * (2 - ratio ^ verticalDepth * outerY) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_right power_order (by linarith : 0 ≤ 2 - ratio ^ verticalDepth * outerY)
    have threshold := below_onset_quadratic ratio positive.le below_onset
    have square_lower : 2 * ratio ≤ outerX ^ 2 := by nlinarith
    have left_lower : ratio ^ (2 * horizontalDepth) * (2 * ratio) ≤
        ratio ^ (2 * horizontalDepth) * outerX ^ 2 :=
      mul_le_mul_of_nonneg_left square_lower (pow_nonneg positive.le _)
    have strict_upper : (ratio ^ (2 * horizontalDepth) * ratio) *
        (2 - ratio ^ verticalDepth * outerY) < ratio ^ (2 * horizontalDepth) * (2 * ratio) := by
      nlinarith [mul_pos (mul_pos (pow_pos positive (2 * horizontalDepth)) positive) deficit_positive]
    linarith

theorem circle_axis_only {ratio x y : ℝ} (positive : 0 < ratio)
    (below_onset : ratio ≤ onset)
    (x_membership : x ∈ cantorSet ratio) (y_membership : y ∈ cantorSet ratio)
    (equation : x ^ 2 + y ^ 2 = 1) :
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  have small : ratio < (1 / 3 : ℝ) := lt_of_le_of_lt below_onset onset_lt_one_third
  have less_one : ratio < 1 := by linarith
  have x_bounds := cantorSet_subset_unitInterval positive.le less_one x_membership
  have y_bounds := cantorSet_subset_unitInterval positive.le less_one y_membership
  by_cases x_zero : x = 0
  · left
    constructor
    · exact x_zero
    · nlinarith [y_bounds.1]
  by_cases y_zero : y = 0
  · right
    constructor
    · nlinarith [x_bounds.1]
    · exact y_zero
  have x_not_one : x ≠ 1 := by intro one; apply y_zero; nlinarith [y_bounds.1]
  have y_not_one : y ≠ 1 := by intro one; apply x_zero; nlinarith [x_bounds.1]
  rcases cantor_first_level_bounds positive.le less_one x_membership with x_left | x_right <;>
    rcases cantor_first_level_bounds positive.le less_one y_membership with y_left | y_right
  · have x_square : x ^ 2 ≤ ratio ^ 2 := by nlinarith [x_bounds.1]
    have y_square : y ^ 2 ≤ ratio ^ 2 := by nlinarith [y_bounds.1]
    nlinarith [mul_pos positive (sub_pos.mpr small)]
  · exact False.elim (no_nonaxis_ordered positive below_onset x_membership y_membership
      x_left y_right x_zero y_not_one equation)
  · exact False.elim (no_nonaxis_ordered positive below_onset y_membership x_membership
      y_left x_right y_zero x_not_one (by nlinarith))
  · have x_square : (1 - ratio) ^ 2 ≤ x ^ 2 := by nlinarith [x_bounds.1]
    have y_square : (1 - ratio) ^ 2 ≤ y ^ 2 := by nlinarith [y_bounds.1]
    have smaller := lt_of_le_of_lt below_onset onset_lt_twenty_seven_hundredths
    nlinarith [sq_nonneg (ratio - 27 / 100)]

end LambdaCantor.Circle
