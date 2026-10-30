import LambdaCantor.Circle.PowerDerivativeBounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp

namespace LambdaCantor.Circle

/-- Product-rule estimate for the three positive residual terms. The power
and tail estimates supplied below are exact rational inequalities. -/
theorem residual_derivative_error_bound
    (firstPower secondPower thirdPower firstPowerDerivative secondPowerDerivative thirdPowerDerivative
      firstFactor firstFactorDerivative firstTail firstTailDerivative lastFactor lastFactorDerivative : ℝ)
    (first_power : |firstPower| ≤ 1 / 100) (second_power : |secondPower| ≤ 1 / 100)
    (third_power : |thirdPower| ≤ 1 / 100)
    (first_derivative : |firstPowerDerivative| ≤ 1 / 10)
    (second_derivative : |secondPowerDerivative| ≤ 1 / 10)
    (third_derivative : |thirdPowerDerivative| ≤ 1 / 10)
    (first_factor : |firstFactor| ≤ 2) (first_factor_derivative : |firstFactorDerivative| ≤ 7)
    (tail_bound : |firstTail| ≤ 1) (tail_derivative : |firstTailDerivative| ≤ 3)
    (last_factor : |lastFactor| ≤ 1) (last_factor_derivative : |lastFactorDerivative| ≤ 13 / 100) :
    |2 * (firstPowerDerivative * firstFactor + firstPower * firstFactorDerivative) +
      (secondPowerDerivative * firstTail ^ 2 + secondPower * (2 * firstTail * firstTailDerivative)) +
      (thirdPowerDerivative * lastFactor ^ 2 + thirdPower * (2 * lastFactor * lastFactorDerivative))| < 1 := by
  have first_bound : |2 * (firstPowerDerivative * firstFactor + firstPower * firstFactorDerivative)| ≤ 54 / 100 := by
    calc
      _ ≤ 2 * (|firstPowerDerivative| * |firstFactor| + |firstPower| * |firstFactorDerivative|) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_add_le (firstPowerDerivative * firstFactor) (firstPower * firstFactorDerivative)) (by norm_num)
      _ ≤ 2 * ((1 / 10) * 2 + (1 / 100) * 7) := by gcongr
      _ = _ := by norm_num
  have second_bound : |secondPowerDerivative * firstTail ^ 2 + secondPower * (2 * firstTail * firstTailDerivative)| ≤ 16 / 100 := by
    calc
      _ ≤ |secondPowerDerivative| * |firstTail| ^ 2 + |secondPower| * (2 * |firstTail| * |firstTailDerivative|) := by
        have triangle := abs_add_le (secondPowerDerivative * firstTail ^ 2)
          (secondPower * (2 * firstTail * firstTailDerivative))
        rw [abs_mul secondPowerDerivative (firstTail ^ 2), abs_pow firstTail 2] at triangle
        simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using triangle
      _ ≤ (1 / 10) * 1 ^ 2 + (1 / 100) * (2 * 1 * 3) := by gcongr
      _ = _ := by norm_num
  have third_bound : |thirdPowerDerivative * lastFactor ^ 2 + thirdPower * (2 * lastFactor * lastFactorDerivative)| ≤ 1026 / 10000 := by
    calc
      _ ≤ |thirdPowerDerivative| * |lastFactor| ^ 2 + |thirdPower| * (2 * |lastFactor| * |lastFactorDerivative|) := by
        have triangle := abs_add_le (thirdPowerDerivative * lastFactor ^ 2)
          (thirdPower * (2 * lastFactor * lastFactorDerivative))
        rw [abs_mul thirdPowerDerivative (lastFactor ^ 2), abs_pow lastFactor 2] at triangle
        simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using triangle
      _ ≤ (1 / 10) * 1 ^ 2 + (1 / 100) * (2 * 1 * (13 / 100)) := by gcongr
      _ = _ := by norm_num
  have first_triangle := abs_add_le
    (2 * (firstPowerDerivative * firstFactor + firstPower * firstFactorDerivative))
    (secondPowerDerivative * firstTail ^ 2 + secondPower * (2 * firstTail * firstTailDerivative))
  have second_triangle := abs_add_le
    (2 * (firstPowerDerivative * firstFactor + firstPower * firstFactorDerivative) +
      (secondPowerDerivative * firstTail ^ 2 + secondPower * (2 * firstTail * firstTailDerivative)))
    (thirdPowerDerivative * lastFactor ^ 2 + thirdPower * (2 * lastFactor * lastFactorDerivative))
  linarith

end LambdaCantor.Circle
