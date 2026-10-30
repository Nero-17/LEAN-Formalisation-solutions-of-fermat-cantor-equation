import LambdaCantor.AE.MixedEnvelopeBounds

noncomputable section

namespace LambdaCantor.AE

def centeredMixedConstant (exponent lower upper discrepancyBound resonanceBound exponentBound normalizedBound : ℝ) : ℝ :=
  (exponent+exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
      (1/lower+2*addressParameterDerivativeBound upper) +
    exponent*resonanceBound*((discrepancyBound+1)/lower+2*addressParameterDerivativeBound upper) +
    (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
      ((exponentBound+5)/lower+3*addressParameterDerivativeBound upper)*normalizedBound

/-- The actual mixed derivative has precisely the uniform rho-times-prefix
scale required for the quadratic Newton error. All phase and normalization
inputs are elementary consequences of the actual centered depth choices. -/
theorem centeredNormalizedResidual_first_prefix_rho_bound
    {exponent lower ratio upper rho discrepancyBound resonanceBound exponentBound normalizedBound : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower)
    (ratio_lower : lower ≤ ratio) (ratio_upper : ratio ≤ upper) (upper_less_one : upper < 1)
    (rho_nonnegative : 0 ≤ rho)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (vertical_large : 1 ≤ verticalDepth) (tail_le_vertical : tailDepth ≤ verticalDepth)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2)
    (tail_rho : ratio^tailDepth ≤ 2*rho)
    (discrepancy_bound : |(verticalDepth : ℝ)-exponent*horizontalDepth| ≤ discrepancyBound)
    (resonance_bound : ratio^((verticalDepth : ℝ)-exponent*horizontalDepth) ≤ resonanceBound)
    (exponent_bound_nonnegative : 0 ≤ exponentBound)
    (scale_bound : |-exponent*(horizontalDepth : ℝ)| ≤ exponentBound*verticalDepth)
    (normalized_bound : (verticalDepth : ℝ)^2*
      (ratio^(-exponent*(horizontalDepth : ℝ))*(ratio^verticalDepth)^2) ≤ normalizedBound)
    (first second : ℕ → Bool × Bool) (agreement : ∀ index < depth, first index = second index) :
    |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth first) ratio -
      deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth second) ratio| ≤
      2*centeredMixedConstant exponent lower upper discrepancyBound resonanceBound exponentBound normalizedBound *
        rho*(((tailDepth+depth+1 : ℕ) : ℝ))*upper^depth := by
  have positive := lower_positive.trans_le ratio_lower
  have upper_positive : 0 < upper := positive.trans_le ratio_upper
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := sub_pos.mpr exponent_greater_one
  have discrepancy_nonnegative := (abs_nonneg _).trans discrepancy_bound
  have resonance_nonnegative := (Real.rpow_nonneg positive.le _).trans resonance_bound
  have normalized_nonnegative : 0 ≤ normalizedBound :=
    (mul_nonneg (sq_nonneg _) (mul_nonneg (Real.rpow_nonneg positive.le _) (sq_nonneg _))).trans normalized_bound
  have address_nonnegative : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg _).trans (address_parameter_derivative_bound positive.le ratio_upper upper_less_one (fun _ => false))
  have constant_nonnegative :
      0 ≤ centeredMixedConstant exponent lower upper discrepancyBound resonanceBound exponentBound normalizedBound := by
    unfold centeredMixedConstant
    positivity
  have horizontal := centeredHorizontalPrefixEnvelope_scale_bound exponent_greater_one lower_positive
    ratio_lower ratio_upper upper_less_one tailDepth depth
  have linear := centeredLinearPrefixEnvelope_scale_bound exponent_positive.le lower_positive ratio_lower ratio_upper
    upper_less_one horizontalDepth verticalDepth tailDepth depth discrepancy_bound resonance_bound
  have remainder := centeredRemainderPrefixEnvelope_scale_bound exponent_greater_one lower_positive ratio_lower ratio_upper
    upper_less_one horizontalDepth verticalDepth tailDepth depth vertical_large tail_le_vertical
    exponent_bound_nonnegative scale_bound normalized_bound
  have length_bound : ((depth+1 : ℕ) : ℝ) ≤ ((tailDepth+depth+1 : ℕ) : ℝ) := by
    exact_mod_cast (show depth+1 ≤ tailDepth+depth+1 by omega)
  have remainder_extended : centeredRemainderPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper ≤
      (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        ((exponentBound+5)/lower+3*addressParameterDerivativeBound upper)*normalizedBound *
          (((tailDepth+depth+1 : ℕ) : ℝ))*ratio^tailDepth*ratio^depth := by
    apply remainder.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left length_bound (by positivity))
        (pow_nonneg positive.le tailDepth)) (pow_nonneg positive.le depth)
  have mixed := centeredNormalizedResidual_first_shared_prefix_bound exponent_greater_one positive ratio_upper upper_less_one
    horizontalDepth verticalDepth tailDepth depth tail_small vertical_small first second agreement
  have common_bound :
      centeredHorizontalPrefixEnvelope exponent tailDepth depth ratio upper +
        centeredLinearPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper +
        centeredRemainderPrefixEnvelope exponent horizontalDepth verticalDepth tailDepth depth ratio upper ≤
      centeredMixedConstant exponent lower upper discrepancyBound resonanceBound exponentBound normalizedBound *
        (((tailDepth+depth+1 : ℕ) : ℝ))*ratio^tailDepth*ratio^depth := by
    apply (add_le_add (add_le_add horizontal linear) remainder_extended).trans_eq
    unfold centeredMixedConstant
    ring
  apply (mixed.trans common_bound).trans
  have upper_power := pow_le_pow_left₀ positive.le ratio_upper depth
  have scaled := mul_le_mul
    (mul_le_mul_of_nonneg_left tail_rho (by positivity : 0 ≤
      centeredMixedConstant exponent lower upper discrepancyBound resonanceBound exponentBound normalizedBound *
        (((tailDepth+depth+1 : ℕ) : ℝ)))) upper_power
    (pow_nonneg positive.le depth) (by positivity)
  apply scaled.trans_eq
  ring

end LambdaCantor.AE
