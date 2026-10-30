import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace LambdaCantor.AE

theorem nat_power_first_scale_bound (depth : ℕ) {lower ratio : ℝ}
    (lower_positive : 0 < lower) (ratio_lower : lower ≤ ratio) :
    (depth : ℝ)*ratio^(depth-1) ≤ ((depth : ℝ)/lower)*ratio^depth := by
  have ratio_positive := lower_positive.trans_le ratio_lower
  have identity : ratio*((depth : ℝ)*ratio^(depth-1)) = (depth : ℝ)*ratio^depth := by
    cases depth with
    | zero => simp
    | succ depth => simp only [Nat.succ_sub_one, pow_succ]; ring
  have estimate := mul_le_mul_of_nonneg_right ratio_lower
    (show 0 ≤ (depth : ℝ)*ratio^(depth-1) by positivity)
  rw [identity] at estimate
  have quotient : (depth : ℝ)*ratio^(depth-1) ≤ ((depth : ℝ)*ratio^depth)/lower :=
    (le_div_iff₀ lower_positive).mpr (by simpa only [mul_comm] using estimate)
  convert quotient using 1 <;> ring

theorem mixed_remainder_coefficient_bound
    {lower verticalDepth tailDepth depth exponentBound addressBound : ℝ}
    (lower_positive : 0 < lower) (vertical_ge_one : 1 ≤ verticalDepth)
    (tail_nonnegative : 0 ≤ tailDepth) (tail_le_vertical : tailDepth ≤ verticalDepth)
    (depth_nonnegative : 0 ≤ depth) (exponent_nonnegative : 0 ≤ exponentBound)
    (address_nonnegative : 0 ≤ addressBound) :
    (exponentBound*verticalDepth + 2*verticalDepth + 2*tailDepth + depth)/lower + 3*addressBound ≤
      ((exponentBound+5)/lower + 3*addressBound)*verticalDepth^2*(depth+1) := by
  have vertical_nonnegative : 0 ≤ verticalDepth := by linarith
  have square_ge_vertical : verticalDepth ≤ verticalDepth^2 := by nlinarith
  have factor_ge_square : verticalDepth^2 ≤ verticalDepth^2*(depth+1) := by
    nlinarith [mul_nonneg (sq_nonneg verticalDepth) depth_nonnegative]
  have factor_ge_vertical := square_ge_vertical.trans factor_ge_square
  have square_ge_one : 1 ≤ verticalDepth^2 := by nlinarith
  have factor_ge_depth : depth ≤ verticalDepth^2*(depth+1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr square_ge_one) (by linarith : 0 ≤ depth+1)]
  have factor_ge_one : 1 ≤ verticalDepth^2*(depth+1) := square_ge_one.trans factor_ge_square
  have coefficient_bound :
      exponentBound*verticalDepth + 2*verticalDepth + 2*tailDepth + depth ≤
        (exponentBound+5)*(verticalDepth^2*(depth+1)) := by
    have exponent_term := mul_le_mul_of_nonneg_left factor_ge_vertical exponent_nonnegative
    nlinarith
  calc
    _ ≤ ((exponentBound+5)*(verticalDepth^2*(depth+1)))/lower +
        3*addressBound*(verticalDepth^2*(depth+1)) :=
      add_le_add (div_le_div_of_nonneg_right coefficient_bound lower_positive.le)
        (le_mul_of_one_le_right (by positivity) factor_ge_one)
    _ = _ := by ring

theorem mixed_horizontal_coefficient_bound
    {lower tailDepth depth exponent secondBound addressBound : ℝ}
    (lower_positive : 0 < lower) (tail_nonnegative : 0 ≤ tailDepth) (depth_nonnegative : 0 ≤ depth)
    (exponent_nonnegative : 0 ≤ exponent) (second_nonnegative : 0 ≤ secondBound)
    (address_nonnegative : 0 ≤ addressBound) :
    exponent*((tailDepth+depth)/lower+2*addressBound) + secondBound*(tailDepth/lower+addressBound) ≤
      (exponent+secondBound)*(1/lower+2*addressBound)*(tailDepth+depth+1) := by
  have factor_ge_one : 1 ≤ tailDepth+depth+1 := by linarith
  have first_bound : (tailDepth+depth)/lower+2*addressBound ≤
      (1/lower+2*addressBound)*(tailDepth+depth+1) := by
    have inverse_nonnegative : 0 ≤ lower⁻¹ := inv_nonneg.mpr lower_positive.le
    have address_term := le_mul_of_one_le_right (show 0 ≤ 2*addressBound by positivity) factor_ge_one
    simp only [div_eq_mul_inv] at *
    nlinarith
  have second_bound : tailDepth/lower+addressBound ≤
      (1/lower+2*addressBound)*(tailDepth+depth+1) := by
    apply le_trans _ first_bound
    have inverse_nonnegative : 0 ≤ lower⁻¹ := inv_nonneg.mpr lower_positive.le
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg inverse_nonnegative depth_nonnegative]
  apply (add_le_add
    (mul_le_mul_of_nonneg_left first_bound exponent_nonnegative)
    (mul_le_mul_of_nonneg_left second_bound second_nonnegative)).trans_eq
  ring

theorem mixed_linear_coefficient_bound
    {lower tailDepth depth discrepancyBound addressBound : ℝ}
    (lower_positive : 0 < lower) (tail_nonnegative : 0 ≤ tailDepth) (depth_nonnegative : 0 ≤ depth)
    (discrepancy_nonnegative : 0 ≤ discrepancyBound) (address_nonnegative : 0 ≤ addressBound) :
    (discrepancyBound+tailDepth+depth)/lower+2*addressBound ≤
      ((discrepancyBound+1)/lower+2*addressBound)*(tailDepth+depth+1) := by
  have factor_ge_one : 1 ≤ tailDepth+depth+1 := by linarith
  have numerator_bound : discrepancyBound+tailDepth+depth ≤
      (discrepancyBound+1)*(tailDepth+depth+1) := by
    nlinarith [mul_nonneg discrepancy_nonnegative (add_nonneg tail_nonnegative depth_nonnegative)]
  have address_term := le_mul_of_one_le_right (show 0 ≤ 2*addressBound by positivity) factor_ge_one
  apply (add_le_add (div_le_div_of_nonneg_right numerator_bound lower_positive.le) address_term).trans_eq
  ring

theorem horizontal_mixed_expression_bound
    {lower tailDepth depth tailPower depthPower tailDerivative depthDerivative exponent secondBound addressBound : ℝ}
    (lower_positive : 0 < lower) (tail_nonnegative : 0 ≤ tailDepth) (depth_nonnegative : 0 ≤ depth)
    (tail_power_nonnegative : 0 ≤ tailPower) (tail_power_one : tailPower ≤ 1) (depth_power_nonnegative : 0 ≤ depthPower)
    (exponent_nonnegative : 0 ≤ exponent) (second_nonnegative : 0 ≤ secondBound) (address_nonnegative : 0 ≤ addressBound)
    (tail_derivative : tailDerivative ≤ (tailDepth/lower)*tailPower)
    (depth_derivative : depthDerivative ≤ (depth/lower)*depthPower) :
    exponent*(tailDerivative*depthPower+tailPower*(depthDerivative+2*addressBound*depthPower)) +
      secondBound*(tailPower*depthPower)*(tailDerivative+tailPower*addressBound) ≤
      (exponent+secondBound)*(1/lower+2*addressBound)*(tailDepth+depth+1)*tailPower*depthPower := by
  have tail_coefficient_nonnegative : 0 ≤ tailDepth/lower+addressBound := by positivity
  have tail_coefficient_bound : tailPower*(tailDepth/lower+addressBound) ≤ tailDepth/lower+addressBound :=
    mul_le_of_le_one_left tail_coefficient_nonnegative tail_power_one
  have coefficient_bound := mixed_horizontal_coefficient_bound lower_positive tail_nonnegative depth_nonnegative
    exponent_nonnegative second_nonnegative address_nonnegative
  calc
    _ ≤ exponent*(((tailDepth/lower)*tailPower)*depthPower +
          tailPower*((depth/lower)*depthPower+2*addressBound*depthPower)) +
        secondBound*(tailPower*depthPower)*((tailDepth/lower)*tailPower+tailPower*addressBound) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ exponent_nonnegative
        exact add_le_add (mul_le_mul_of_nonneg_right tail_derivative depth_power_nonnegative)
          (mul_le_mul_of_nonneg_left (add_le_add depth_derivative (le_refl _)) tail_power_nonnegative)
      · exact mul_le_mul_of_nonneg_left (add_le_add tail_derivative (le_refl _))
          (by positivity)
    _ = (exponent*((tailDepth+depth)/lower+2*addressBound) +
        secondBound*(tailPower*(tailDepth/lower+addressBound)))*tailPower*depthPower := by ring
    _ ≤ (exponent*((tailDepth+depth)/lower+2*addressBound) +
        secondBound*(tailDepth/lower+addressBound))*tailPower*depthPower := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left tail_coefficient_bound second_nonnegative))
          tail_power_nonnegative) depth_power_nonnegative
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right coefficient_bound tail_power_nonnegative) depth_power_nonnegative

theorem normalized_remainder_mixed_expression_bound
    {lower verticalDepth tailDepth depth exponentBound addressBound secondBound normalization
      verticalPower tailPower depthPower normalizedBound : ℝ}
    (lower_positive : 0 < lower) (vertical_ge_one : 1 ≤ verticalDepth)
    (tail_nonnegative : 0 ≤ tailDepth) (tail_le_vertical : tailDepth ≤ verticalDepth)
    (depth_nonnegative : 0 ≤ depth) (exponent_nonnegative : 0 ≤ exponentBound)
    (address_nonnegative : 0 ≤ addressBound) (second_nonnegative : 0 ≤ secondBound)
    (normalization_nonnegative : 0 ≤ normalization) (vertical_power_nonnegative : 0 ≤ verticalPower)
    (tail_power_nonnegative : 0 ≤ tailPower) (tail_power_one : tailPower ≤ 1)
    (depth_power_nonnegative : 0 ≤ depthPower)
    (normalized_bound : verticalDepth^2*(normalization*verticalPower^2) ≤ normalizedBound) :
    (exponentBound*verticalDepth)*(normalization/lower)*(secondBound*verticalPower*(verticalPower*tailPower*depthPower)) +
      normalization*((secondBound*verticalPower)*
        (((verticalDepth+tailDepth)/lower)*(verticalPower*tailPower)*depthPower +
          (verticalPower*tailPower)*((depth/lower)*depthPower+2*addressBound*depthPower)) +
        (secondBound*(verticalPower*tailPower*depthPower))*
          ((verticalDepth/lower)*verticalPower + verticalPower*((tailDepth/lower)*tailPower+tailPower*addressBound))) ≤
      secondBound*((exponentBound+5)/lower+3*addressBound)*normalizedBound*(depth+1)*tailPower*depthPower := by
  have tail_coefficient_nonnegative : 0 ≤ tailDepth/lower+addressBound := by positivity
  have tail_coefficient := mul_le_of_le_one_left tail_coefficient_nonnegative tail_power_one
  have coefficient :
      (exponentBound*verticalDepth+2*verticalDepth+tailDepth+depth)/lower+2*addressBound+
          tailPower*(tailDepth/lower+addressBound) ≤
        ((exponentBound+5)/lower+3*addressBound)*verticalDepth^2*(depth+1) := by
    calc
      _ ≤ (exponentBound*verticalDepth+2*verticalDepth+tailDepth+depth)/lower+2*addressBound+
          (tailDepth/lower+addressBound) := add_le_add (le_refl _) tail_coefficient
      _ = (exponentBound*verticalDepth+2*verticalDepth+2*tailDepth+depth)/lower+3*addressBound := by ring
      _ ≤ _ := mixed_remainder_coefficient_bound lower_positive vertical_ge_one tail_nonnegative
        tail_le_vertical depth_nonnegative exponent_nonnegative address_nonnegative
  calc
    _ = secondBound*(normalization*verticalPower^2)*tailPower*depthPower*
        ((exponentBound*verticalDepth+2*verticalDepth+tailDepth+depth)/lower+2*addressBound+
          tailPower*(tailDepth/lower+addressBound)) := by ring
    _ ≤ secondBound*(normalization*verticalPower^2)*tailPower*depthPower*
        (((exponentBound+5)/lower+3*addressBound)*verticalDepth^2*(depth+1)) :=
      mul_le_mul_of_nonneg_left coefficient (by positivity)
    _ = secondBound*((exponentBound+5)/lower+3*addressBound)*
        (verticalDepth^2*(normalization*verticalPower^2))*(depth+1)*tailPower*depthPower := by ring
    _ ≤ _ := by
      have outside_nonnegative : 0 ≤ secondBound*((exponentBound+5)/lower+3*addressBound) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left normalized_bound outside_nonnegative)
            (by linarith : 0 ≤ depth+1)) tail_power_nonnegative) depth_power_nonnegative

end LambdaCantor.AE
