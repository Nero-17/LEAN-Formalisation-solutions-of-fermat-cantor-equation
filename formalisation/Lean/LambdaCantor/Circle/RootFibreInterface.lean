import LambdaCantor.Circle.FixedPrefixes
import LambdaCantor.Circle.CompactRootBand

noncomputable section
namespace LambdaCantor.Circle
open LambdaCantor.First.Roots

theorem circle_cylinders_equation_of_residual_zero {ratio : ℝ} (depth : ℕ)
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1) (firstDigits secondDigits : ℕ → Bool)
    (zero : expandedCircleResidual depth (fun parameter => address parameter firstDigits)
      (fun parameter => address parameter secondDigits) ratio = 0) :
    (address ratio (cylinderDigits (circleHorizontalPrefix depth) (3 * depth + 1) firstDigits)) ^ (2 : ℝ) +
    (address ratio (cylinderDigits (circleVerticalPrefix depth) (4 * depth + 1) secondDigits)) ^ (2 : ℝ) = 1 := by
  have coordinates := circle_cylinder_coordinates depth nonnegative less_one firstDigits secondDigits
  rw [Real.rpow_two, Real.rpow_two, coordinates.1, coordinates.2]
  have identity := root_residual_identity ratio (ratio ^ depth)
    (address ratio firstDigits) (address ratio secondDigits)
  rw [expandedCircleResidual_eq] at zero
  unfold circleRootResidual at zero
  rw [zero, mul_zero] at identity
  linarith

/-- The selected continuous root map solves the actual power-curve equation
on the two specified complete Cantor cylinders, with exponent exactly two. -/
theorem circleAddressRoot_cylinder_equation (depth : ℕ) (large : 2 ≤ depth)
    (digits : ℕ → Bool × Bool) :
    (address (circleAddressRoot depth large digits)
      (cylinderDigits (circleHorizontalPrefix depth) (3 * depth + 1) (fun index => (digits index).1))) ^ (2 : ℝ) +
    (address (circleAddressRoot depth large digits)
      (cylinderDigits (circleVerticalPrefix depth) (4 * depth + 1) (fun index => (digits index).2))) ^ (2 : ℝ) = 1 := by
  have specification := circleAddressRoot_spec depth large digits
  exact circle_cylinders_equation_of_residual_zero depth
    (lt_trans onset_pos specification.1.1).le (lt_trans specification.1.2 (by norm_num))
    _ _ specification.2

end LambdaCantor.Circle
