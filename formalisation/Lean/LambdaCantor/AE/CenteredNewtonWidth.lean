import LambdaCantor.AE.CenteredNewtonCoefficients
import Mathlib.Tactic.GCongr

noncomputable section

namespace LambdaCantor.AE

theorem centeredNewtonFirstCoefficient_bounds
    {exponent ratio prefixBound : ℝ} (exponent_ge_one : 1 ≤ exponent)
    (positive : 0 < ratio) (tailDepth depth : ℕ)
    (base_lower : (1/2 : ℝ) ≤ 1-ratio^tailDepth+ratio^tailDepth*prefixBound)
    (base_upper : 1-ratio^tailDepth+ratio^tailDepth*prefixBound ≤ 1) :
    exponent*(1/2 : ℝ)^(exponent-1)*ratio^tailDepth*ratio^depth ≤
        centeredNewtonFirstCoefficient exponent tailDepth depth ratio prefixBound ∧
      centeredNewtonFirstCoefficient exponent tailDepth depth ratio prefixBound ≤
        exponent*ratio^tailDepth*ratio^depth := by
  have exponent_nonnegative : 0 ≤ exponent := by linarith
  have power_nonnegative : 0 ≤ exponent-1 := by linarith
  have base_nonnegative : 0 ≤ 1-ratio^tailDepth+ratio^tailDepth*prefixBound := by linarith
  have lower := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1/2) base_lower power_nonnegative
  have upper := Real.rpow_le_one base_nonnegative base_upper power_nonnegative
  unfold centeredNewtonFirstCoefficient
  rw [pow_add]
  constructor
  · simpa only [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left lower
        (show 0 ≤ exponent*(ratio^tailDepth*ratio^depth) by positivity)
  · simpa only [mul_one, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left upper
        (show 0 ≤ exponent*(ratio^tailDepth*ratio^depth) by positivity)

theorem centeredNewtonSecondCoefficient_normalized
    (exponent : ℝ) (horizontalDepth verticalDepth tailDepth depth : ℕ)
    {ratio : ℝ} (positive : 0 < ratio) (prefixBound : ℝ) :
    centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth ratio prefixBound =
      exponent*ratio^((verticalDepth : ℝ)-exponent*horizontalDepth)*ratio^tailDepth*ratio^depth*
        (1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*prefixBound)^(exponent-1) := by
  have resonance : ratio^((verticalDepth : ℝ)-exponent*horizontalDepth) =
      ratio^verticalDepth/ratio^(exponent*horizontalDepth) := by
    rw [Real.rpow_sub positive, Real.rpow_natCast]
  unfold centeredNewtonSecondCoefficient
  rw [resonance, pow_add ratio (verticalDepth+tailDepth) depth, pow_add ratio verticalDepth tailDepth]
  ring

theorem centeredNewtonSecondCoefficient_bounds
    {exponent ratio prefixBound resonanceLower resonanceUpper : ℝ} (exponent_ge_one : 1 ≤ exponent)
    (positive : 0 < ratio) (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (resonance_lower_nonnegative : 0 ≤ resonanceLower)
    (resonance_lower : resonanceLower ≤ ratio^((verticalDepth : ℝ)-exponent*horizontalDepth))
    (resonance_upper : ratio^((verticalDepth : ℝ)-exponent*horizontalDepth) ≤ resonanceUpper)
    (base_lower : (1/2 : ℝ) ≤ 1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*prefixBound)
    (base_upper : 1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*prefixBound ≤ 1) :
    exponent*resonanceLower*(1/2 : ℝ)^(exponent-1)*ratio^tailDepth*ratio^depth ≤
        centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth ratio prefixBound ∧
      centeredNewtonSecondCoefficient exponent horizontalDepth verticalDepth tailDepth depth ratio prefixBound ≤
        exponent*resonanceUpper*ratio^tailDepth*ratio^depth := by
  have exponent_nonnegative : 0 ≤ exponent := by linarith
  have power_nonnegative : 0 ≤ exponent-1 := by linarith
  have base_nonnegative : 0 ≤ 1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*prefixBound := by linarith
  have power_lower := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1/2) base_lower power_nonnegative
  have power_upper := Real.rpow_le_one base_nonnegative base_upper power_nonnegative
  have resonance_nonnegative := (Real.rpow_pos_of_pos positive
    ((verticalDepth : ℝ)-exponent*horizontalDepth)).le
  rw [centeredNewtonSecondCoefficient_normalized exponent horizontalDepth verticalDepth tailDepth depth positive prefixBound]
  constructor
  · calc
      _ = exponent*ratio^tailDepth*ratio^depth*(resonanceLower*(1/2 : ℝ)^(exponent-1)) := by ring
      _ ≤ exponent*ratio^tailDepth*ratio^depth*
          (ratio^((verticalDepth : ℝ)-exponent*horizontalDepth)*
            (1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*prefixBound)^(exponent-1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul resonance_lower power_lower (by positivity) resonance_nonnegative
      _ = _ := by ring
  · calc
      _ = exponent*ratio^tailDepth*ratio^depth*
          (ratio^((verticalDepth : ℝ)-exponent*horizontalDepth)*
            (1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*prefixBound)^(exponent-1)) := by ring
      _ ≤ exponent*ratio^tailDepth*ratio^depth*resonanceUpper := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_left power_upper resonance_nonnegative).trans
          (by simpa only [mul_one] using resonance_upper)
      _ = _ := by ring

/-- Uniform transverse derivative bounds turn the actual positive tail
coefficients into the physical kernel widths, without losing their prefix scale. -/
theorem newton_coefficient_div_slope_bounds
    {coefficient coefficientLower coefficientUpper derivative slope derivativeBound : ℝ}
    (coefficient_lower_nonnegative : 0 ≤ coefficientLower)
    (coefficient_lower : coefficientLower ≤ coefficient) (coefficient_upper : coefficient ≤ coefficientUpper)
    (slope_positive : 0 < slope) (derivative_negative : derivative ≤ -slope)
    (derivative_bound : |derivative| ≤ derivativeBound) :
    coefficientLower/derivativeBound ≤ -coefficient/derivative ∧
      -coefficient/derivative ≤ coefficientUpper/slope := by
  have derivative_negative_strict : derivative < 0 := by linarith
  have absolute_positive := abs_pos.mpr derivative_negative_strict.ne
  have absolute_lower : slope ≤ |derivative| := by rw [abs_of_neg derivative_negative_strict]; linarith
  have derivativeBound_positive := absolute_positive.trans_le derivative_bound
  have coefficient_nonnegative := coefficient_lower_nonnegative.trans coefficient_lower
  have identity : -coefficient/derivative = coefficient/|derivative| := by
    rw [abs_of_neg derivative_negative_strict, div_neg, neg_div]
  rw [identity]
  constructor
  · exact (div_le_div_of_nonneg_left coefficient_lower_nonnegative absolute_positive derivative_bound).trans
      (div_le_div_of_nonneg_right coefficient_lower absolute_positive.le)
  · exact (div_le_div_of_nonneg_left coefficient_nonnegative slope_positive absolute_lower).trans
      (div_le_div_of_nonneg_right coefficient_upper slope_positive.le)

end LambdaCantor.AE
