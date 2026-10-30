import LambdaCantor.AE.CenteredMixedDerivative
import LambdaCantor.AE.MixedScaleArithmetic

noncomputable section

namespace LambdaCantor.AE

theorem centeredHorizontalPrefixEnvelope_scale_bound
    {exponent lower ratio upper : ℝ} (exponent_greater_one : 1 < exponent)
    (lower_positive : 0 < lower) (ratio_lower : lower ≤ ratio) (ratio_upper : ratio ≤ upper)
    (upper_less_one : upper < 1) (tailDepth depth : ℕ) :
    centeredHorizontalPrefixEnvelope exponent tailDepth depth ratio upper ≤
      (exponent+exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        (1/lower+2*addressParameterDerivativeBound upper) *
          (((tailDepth+depth+1 : ℕ) : ℝ))*ratio^tailDepth*ratio^depth := by
  have positive := lower_positive.trans_le ratio_lower
  have less_one := ratio_upper.trans_lt upper_less_one
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := sub_pos.mpr exponent_greater_one
  have address_nonnegative : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg _).trans (address_parameter_derivative_bound positive.le ratio_upper upper_less_one (fun _ => false))
  have bound := horizontal_mixed_expression_bound lower_positive
    (Nat.cast_nonneg tailDepth) (Nat.cast_nonneg depth)
    (pow_nonneg positive.le tailDepth) (pow_le_one₀ positive.le less_one.le)
    (pow_nonneg positive.le depth) exponent_positive.le (by positivity) address_nonnegative
    (nat_power_first_scale_bound tailDepth lower_positive ratio_lower)
    (nat_power_first_scale_bound depth lower_positive ratio_lower)
    (secondBound := exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))
  simpa only [centeredHorizontalPrefixEnvelope, Nat.cast_add, Nat.cast_one] using bound

theorem centeredLinearPrefixEnvelope_scale_bound
    {exponent lower ratio upper discrepancyBound resonanceBound : ℝ}
    (exponent_nonnegative : 0 ≤ exponent) (lower_positive : 0 < lower)
    (ratio_lower : lower ≤ ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (discrepancy_bound : |(verticalDepth : ℝ)-exponent*horizontalDepth| ≤ discrepancyBound)
    (resonance_bound : ratio^((verticalDepth : ℝ)-exponent*horizontalDepth) ≤ resonanceBound) :
    centeredLinearPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper ≤
      exponent*resonanceBound*((discrepancyBound+1)/lower+2*addressParameterDerivativeBound upper) *
        (((tailDepth+depth+1 : ℕ) : ℝ))*ratio^tailDepth*ratio^depth := by
  have positive := lower_positive.trans_le ratio_lower
  have discrepancy_nonnegative := (abs_nonneg _).trans discrepancy_bound
  have resonance_nonnegative := (Real.rpow_nonneg positive.le _).trans resonance_bound
  have address_nonnegative : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg _).trans (address_parameter_derivative_bound positive.le ratio_upper upper_less_one (fun _ => false))
  have absolute_coefficient :
      |exponent*((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth)| ≤
        exponent*(discrepancyBound+tailDepth) := by
    rw [abs_mul, abs_of_nonneg exponent_nonnegative]
    apply mul_le_mul_of_nonneg_left _ exponent_nonnegative
    apply (abs_add_le _ _).trans
    simpa only [Nat.abs_cast] using add_le_add discrepancy_bound (le_refl (tailDepth : ℝ))
  have power_bound : ratio^((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth) ≤
      resonanceBound*ratio^tailDepth := by
    rw [Real.rpow_add positive, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right resonance_bound (pow_nonneg positive.le tailDepth)
  have shifted_power : ratio^((verticalDepth : ℝ)-exponent*horizontalDepth+tailDepth-1) ≤
      (resonanceBound/lower)*ratio^tailDepth := by
    rw [Real.rpow_sub positive, Real.rpow_one]
    calc
      _ ≤ (resonanceBound*ratio^tailDepth)/ratio := div_le_div_of_nonneg_right power_bound positive.le
      _ ≤ (resonanceBound*ratio^tailDepth)/lower :=
        div_le_div_of_nonneg_left (by positivity) lower_positive ratio_lower
      _ = _ := by ring
  have depth_derivative := nat_power_first_scale_bound depth lower_positive ratio_lower
  have coefficient := mixed_linear_coefficient_bound lower_positive (Nat.cast_nonneg tailDepth)
    (Nat.cast_nonneg depth) discrepancy_nonnegative address_nonnegative
  unfold centeredLinearPrefixEnvelope
  calc
    _ ≤ (exponent*(discrepancyBound+tailDepth))*((resonanceBound/lower)*ratio^tailDepth)*ratio^depth +
        exponent*(resonanceBound*ratio^tailDepth)*
          (((depth : ℝ)/lower)*ratio^depth+2*addressParameterDerivativeBound upper*ratio^depth) := by
      gcongr <;> first | exact absolute_coefficient | exact shifted_power | exact power_bound |
        exact depth_derivative | positivity
    _ = exponent*resonanceBound*
        ((discrepancyBound+tailDepth+depth)/lower+2*addressParameterDerivativeBound upper)*ratio^tailDepth*ratio^depth := by ring
    _ ≤ _ := by
      have bound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left coefficient (mul_nonneg exponent_nonnegative resonance_nonnegative))
          (pow_nonneg positive.le tailDepth)) (pow_nonneg positive.le depth)
      simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using bound

theorem centeredRemainderPrefixEnvelope_scale_bound
    {exponent lower ratio upper exponentBound normalizedBound : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower)
    (ratio_lower : lower ≤ ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (vertical_large : 1 ≤ verticalDepth) (tail_le_vertical : tailDepth ≤ verticalDepth)
    (exponent_bound_nonnegative : 0 ≤ exponentBound)
    (scale_bound : |-exponent*(horizontalDepth : ℝ)| ≤ exponentBound*verticalDepth)
    (normalized_bound : (verticalDepth : ℝ)^2*
      (ratio^(-exponent*(horizontalDepth : ℝ))*(ratio^verticalDepth)^2) ≤ normalizedBound) :
    centeredRemainderPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper ≤
      (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        ((exponentBound+5)/lower+3*addressParameterDerivativeBound upper) * normalizedBound *
          (((depth+1 : ℕ) : ℝ))*ratio^tailDepth*ratio^depth := by
  have positive := lower_positive.trans_le ratio_lower
  have less_one := ratio_upper.trans_lt upper_less_one
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := sub_pos.mpr exponent_greater_one
  let powerBound := exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))
  have power_bound_nonnegative : 0 ≤ powerBound := by dsimp [powerBound]; positivity
  have address_nonnegative : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg _).trans (address_parameter_derivative_bound positive.le ratio_upper upper_less_one (fun _ => false))
  have vertical_ge_one : (1 : ℝ) ≤ verticalDepth := by exact_mod_cast vertical_large
  have tail_le_vertical_real : (tailDepth : ℝ) ≤ verticalDepth := by exact_mod_cast tail_le_vertical
  have shift := centered_shifted_normalization_bound (scaleExponent := -exponent*(horizontalDepth : ℝ))
    lower_positive ratio_lower 1
  simp only [Nat.cast_one, pow_one] at shift
  have vertical_derivative := nat_power_first_scale_bound verticalDepth lower_positive ratio_lower
  have tail_derivative := nat_power_first_scale_bound tailDepth lower_positive ratio_lower
  have depth_derivative := nat_power_first_scale_bound depth lower_positive ratio_lower
  have combined_derivative := nat_power_first_scale_bound (verticalDepth+tailDepth) lower_positive ratio_lower
  simp only [Nat.cast_add, pow_add] at combined_derivative
  have bound := normalized_remainder_mixed_expression_bound lower_positive vertical_ge_one
    (Nat.cast_nonneg tailDepth) tail_le_vertical_real (Nat.cast_nonneg depth) exponent_bound_nonnegative
    address_nonnegative power_bound_nonnegative (Real.rpow_nonneg positive.le _)
    (pow_nonneg positive.le verticalDepth) (pow_nonneg positive.le tailDepth)
    (pow_le_one₀ positive.le less_one.le) (pow_nonneg positive.le depth) normalized_bound
    (secondBound := powerBound)
  apply le_trans ?_ (by simpa only [powerBound, Nat.cast_add, Nat.cast_one] using bound)
  unfold centeredRemainderPrefixEnvelope
  change _ ≤ _
  simp only [Nat.cast_add, pow_add]
  gcongr ?_ * ?_ *
      ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*ratio^verticalDepth*
        ((ratio^verticalDepth*ratio^tailDepth)*ratio^depth)) +
    ratio^(-exponent*(horizontalDepth : ℝ)) *
      (((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*ratio^verticalDepth)*
        (?_ * ratio^depth + (ratio^verticalDepth*ratio^tailDepth)*
          (?_ + 2*addressParameterDerivativeBound upper*ratio^depth)) +
        ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*
          ((ratio^verticalDepth*ratio^tailDepth)*ratio^depth))*
          (?_ + ratio^verticalDepth*(?_ + ratio^tailDepth*addressParameterDerivativeBound upper))) <;>
    first | exact scale_bound | exact shift | exact combined_derivative |
      exact depth_derivative | exact vertical_derivative | exact tail_derivative | positivity

end LambdaCantor.AE
