import LambdaCantor.Circle.DerivativeError

namespace LambdaCantor.Circle

def circleResidualSlope (depth : ℕ) (ratio firstTail secondTail firstDerivative secondDerivative : ℝ) : ℝ :=
  -4 + 2 * ratio +
    (2 * (((2 * depth + 1 : ℕ) : ℝ) * ratio ^ (2 * depth) * ((1 - ratio) * firstTail + secondTail) +
      ratio ^ (2 * depth + 1) * (-firstTail + (1 - ratio) * firstDerivative + secondDerivative)) +
    (((4 * depth + 2 : ℕ) : ℝ) * ratio ^ (4 * depth + 1) * firstTail ^ 2 +
      ratio ^ (4 * depth + 2) * (2 * firstTail * firstDerivative)) +
    (((2 * depth + 2 : ℕ) : ℝ) * ratio ^ (2 * depth + 1) * (1 - ratio ^ (2 * depth) * secondTail) ^ 2 +
      ratio ^ (2 * depth + 2) * (2 * (1 - ratio ^ (2 * depth) * secondTail) *
        (-((2 * depth : ℕ) : ℝ) * ratio ^ (2 * depth - 1) * secondTail - ratio ^ (2 * depth) * secondDerivative))))

theorem circle_residual_slope_bounds (depth : ℕ) (large : 2 ≤ depth)
    (ratio firstTail secondTail firstDerivative secondDerivative : ℝ)
    (nonnegative : 0 ≤ ratio) (upper : ratio ≤ (7 / 25 : ℝ))
    (first_nonnegative : 0 ≤ firstTail) (first_upper : firstTail ≤ 1)
    (second_nonnegative : 0 ≤ secondTail) (second_upper : secondTail ≤ 1)
    (first_derivative : |firstDerivative| ≤ 3) (second_derivative : |secondDerivative| ≤ 3) :
    -5 < circleResidualSlope depth ratio firstTail secondTail firstDerivative secondDerivative ∧
      circleResidualSlope depth ratio firstTail secondTail firstDerivative secondDerivative < -2 := by
  have small : ratio ≤ 1 := by linarith
  have power_bounds (exponent : ℕ) (at_least_four : 4 ≤ exponent) :
      |ratio ^ exponent| ≤ 1 / 100 ∧
      |(exponent : ℝ) * ratio ^ (exponent - 1)| ≤ 1 / 10 := by
    simpa only [abs_of_nonneg (pow_nonneg nonnegative _),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg nonnegative _))] using
      high_power_bounds nonnegative upper exponent at_least_four
  have first_power := power_bounds (2 * depth + 1) (by omega)
  have second_power := power_bounds (4 * depth + 2) (by omega)
  have third_power := power_bounds (2 * depth + 2) (by omega)
  have inner_power := power_bounds (2 * depth) (by omega)
  have first_factor : |(1 - ratio) * firstTail + secondTail| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr small) first_nonnegative) second_nonnegative)]
    nlinarith [mul_nonneg nonnegative first_nonnegative]
  have first_factor_derivative : |-firstTail + (1 - ratio) * firstDerivative + secondDerivative| ≤ 7 := by
    calc
      _ ≤ |firstTail| + |1 - ratio| * |firstDerivative| + |secondDerivative| := by
        have := abs_add_le (-firstTail) ((1 - ratio) * firstDerivative)
        have := abs_add_le (-firstTail + (1 - ratio) * firstDerivative) secondDerivative
        simp only [abs_neg, abs_mul] at *
        linarith
      _ ≤ 1 + 1 * 3 + 3 := by
        gcongr
        · rwa [abs_of_nonneg first_nonnegative]
        · rw [abs_of_nonneg (sub_nonneg.mpr small)]; linarith
      _ = 7 := by norm_num
  have inner_bounds : 0 ≤ ratio ^ (2 * depth) * secondTail ∧ ratio ^ (2 * depth) * secondTail ≤ 1 := by
    constructor
    · positivity
    · exact mul_le_one₀ (pow_le_one₀ nonnegative small) second_nonnegative second_upper
  have last_factor : |1 - ratio ^ (2 * depth) * secondTail| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr inner_bounds.2)]
    linarith [inner_bounds.1]
  have last_factor_derivative :
      |-((2 * depth : ℕ) : ℝ) * ratio ^ (2 * depth - 1) * secondTail -
        ratio ^ (2 * depth) * secondDerivative| ≤ 13 / 100 := by
    calc
      _ ≤ |((2 * depth : ℕ) : ℝ) * ratio ^ (2 * depth - 1)| * |secondTail| +
          |ratio ^ (2 * depth)| * |secondDerivative| := by
        simpa only [sub_eq_add_neg, abs_mul, abs_neg] using abs_add_le
          (-((2 * depth : ℕ) : ℝ) * ratio ^ (2 * depth - 1) * secondTail)
          (-(ratio ^ (2 * depth) * secondDerivative))
      _ ≤ (1 / 10) * 1 + (1 / 100) * 3 := by
        gcongr
        · exact inner_power.2
        · rwa [abs_of_nonneg second_nonnegative]
        · exact inner_power.1
      _ = _ := by norm_num
  have error := residual_derivative_error_bound
    (ratio ^ (2 * depth + 1)) (ratio ^ (4 * depth + 2)) (ratio ^ (2 * depth + 2))
    (((2 * depth + 1 : ℕ) : ℝ) * ratio ^ (2 * depth))
    (((4 * depth + 2 : ℕ) : ℝ) * ratio ^ (4 * depth + 1))
    (((2 * depth + 2 : ℕ) : ℝ) * ratio ^ (2 * depth + 1))
    ((1 - ratio) * firstTail + secondTail) (-firstTail + (1 - ratio) * firstDerivative + secondDerivative)
    firstTail firstDerivative (1 - ratio ^ (2 * depth) * secondTail)
    (-((2 * depth : ℕ) : ℝ) * ratio ^ (2 * depth - 1) * secondTail - ratio ^ (2 * depth) * secondDerivative)
    first_power.1 second_power.1 third_power.1
    (by simpa using first_power.2) (by simpa using second_power.2) (by simpa using third_power.2)
    first_factor first_factor_derivative (by rwa [abs_of_nonneg first_nonnegative])
    first_derivative last_factor last_factor_derivative
  have error_bounds := abs_lt.mp error
  unfold circleResidualSlope
  constructor <;> linarith [error_bounds.1, error_bounds.2]

end LambdaCantor.Circle

