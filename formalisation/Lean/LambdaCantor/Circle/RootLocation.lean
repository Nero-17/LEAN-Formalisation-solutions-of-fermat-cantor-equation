import LambdaCantor.Circle.RootExistence

noncomputable section
namespace LambdaCantor.Circle

/-- Every constructed root is uniformly close to onset. This estimate uses
only bounded tails and the residual equation; differentiability is unnecessary. -/
theorem circle_root_distance (depth : ℕ) {ratio : ℝ} (firstTail secondTail : ℝ → ℝ)
    (above : onset < ratio) (upper : ratio ≤ (7 / 25 : ℝ))
    (first_nonnegative : 0 ≤ firstTail ratio) (first_upper : firstTail ratio ≤ 1)
    (second_nonnegative : 0 ≤ secondTail ratio) (second_upper : secondTail ratio ≤ 1)
    (root : circleRootResidual depth firstTail secondTail ratio = 0) :
    ratio < onset + 2 * (7 / 25 : ℝ) ^ (2 * depth + 1) := by
  have positive : 0 < ratio := lt_trans onset_pos above
  have less_one : ratio < 1 := by linarith
  have scale_nonnegative := pow_nonneg positive.le depth
  have scale_upper := pow_le_one₀ positive.le less_one.le (n := depth)
  have scale_square : (ratio ^ depth) ^ 2 ≤ 1 := by nlinarith
  have first_square : (firstTail ratio) ^ 2 ≤ 1 := by nlinarith
  have inner_product : (ratio ^ depth) ^ 2 * secondTail ratio ≤ 1 := by
    have := mul_le_mul_of_nonneg_left second_upper (sq_nonneg (ratio ^ depth))
    linarith
  have inner_square : (1 - (ratio ^ depth) ^ 2 * secondTail ratio) ^ 2 ≤ 1 := by
    have := mul_nonneg (sq_nonneg (ratio ^ depth)) second_nonnegative
    nlinarith
  have first_term : 2 * ratio * (ratio ^ depth) ^ 2 *
      ((1 - ratio) * firstTail ratio + secondTail ratio) ≤
      2 * ratio * (ratio ^ depth) ^ 2 * (2 - ratio) := by
    have tails_upper : (1 - ratio) * firstTail ratio + secondTail ratio ≤ 2 - ratio := by
      nlinarith [mul_nonneg (sub_nonneg.mpr less_one.le) (sub_nonneg.mpr first_upper)]
    exact mul_le_mul_of_nonneg_left tails_upper (by positivity)
  have second_term : ratio ^ 2 * (ratio ^ depth) ^ 4 * (firstTail ratio) ^ 2 ≤
      ratio ^ 2 * (ratio ^ depth) ^ 4 := by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ratio) (pow_nonneg scale_nonnegative 4)) (sub_nonneg.mpr first_square)]
  have third_term : ratio ^ 2 * (ratio ^ depth) ^ 2 *
      (1 - (ratio ^ depth) ^ 2 * secondTail ratio) ^ 2 ≤ ratio ^ 2 * (ratio ^ depth) ^ 2 := by
    exact mul_le_of_le_one_right (by positivity) inner_square
  have remainder_nonpositive := mul_nonneg (mul_nonneg (sq_nonneg ratio) (sq_nonneg (ratio ^ depth)))
    (sub_nonneg.mpr scale_square)
  have residual_bound : 4 * ratio - 1 - ratio ^ 2 ≤ 4 * ratio * (ratio ^ depth) ^ 2 := by
    unfold circleRootResidual at root
    nlinarith
  have power_identity : ratio * (ratio ^ depth) ^ 2 = ratio ^ (2 * depth + 1) := by
    calc
      ratio * (ratio ^ depth) ^ 2 = ratio * ratio ^ (depth * 2) :=
        congrArg (fun value : ℝ => ratio * value) (pow_mul ratio depth 2).symm
      _ = ratio * ratio ^ (2 * depth) := by rw [Nat.mul_comm depth 2]
      _ = ratio ^ (2 * depth + 1) := (pow_succ' ratio (2 * depth)).symm
  have power_bound := pow_le_pow_left₀ positive.le upper (2 * depth + 1)
  have endpoint_power := pow_pos (by norm_num : (0 : ℝ) < 7 / 25) (2 * depth + 1)
  have factor_positive : 0 < 1 - ratio - onset := by
    have := onset_lt_one_third
    linarith
  have product_positive := mul_pos (sub_pos.mpr above) factor_positive
  have onset_identity := onset_equation
  have factorization : 4 * ratio - 1 - ratio ^ 2 =
      (ratio - onset) * (4 - ratio - onset) := by nlinarith
  have rewritten : 4 * ratio - 1 - ratio ^ 2 ≤ 4 * ratio ^ (2 * depth + 1) := by
    nlinarith [power_identity]
  nlinarith

end LambdaCantor.Circle
