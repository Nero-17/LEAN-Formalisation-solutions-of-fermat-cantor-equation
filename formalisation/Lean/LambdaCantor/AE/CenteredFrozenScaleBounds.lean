import LambdaCantor.AE.CenteredPrefixTaylor
import LambdaCantor.AE.CenteredNewtonWidth
import LambdaCantor.AE.CenteredResonanceBand
import LambdaCantor.AE.NormalizedNewtonKernel

noncomputable section

namespace LambdaCantor.AE

/-- Actual frozen coefficients give two-sided physical widths on precisely
rho times the freezing parameter to the prefix depth. -/
theorem centeredFrozenNewton_scale_bounds
    {exponent ratio lower rho discrepancyBound slope derivativeBound : ℝ}
    (exponent_greater_one : 1 < exponent) (positive : 0 < ratio) (less_one : ratio < 1)
    (lower_positive : 0 < lower) (ratio_lower : lower ≤ ratio)
    (rho_nonnegative : 0 ≤ rho) (discrepancy_nonnegative : 0 ≤ discrepancyBound)
    (slope_positive : 0 < slope) (derivativeBound_positive : 0 < derivativeBound)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2)
    (tail_lower : rho/2 ≤ ratio^tailDepth) (tail_upper : ratio^tailDepth ≤ 2*rho)
    (phase_bound : |(verticalDepth : ℝ)-exponent*horizontalDepth| ≤ discrepancyBound)
    (derivative_negative :
      deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index)) ratio ≤ -slope)
    (derivative_bound :
      |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index)) ratio| ≤ derivativeBound) :
    ((exponent*(1/2 : ℝ)^(exponent-1)/(2*derivativeBound))*rho*ratio^depth ≤
        (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).firstScale ∧
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).firstScale ≤
        (2*exponent/slope)*rho*ratio^depth) ∧
    ((exponent*lower^discrepancyBound*(1/2 : ℝ)^(exponent-1)/(2*derivativeBound))*rho*ratio^depth ≤
        (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).secondScale ∧
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index) ratio).secondScale ≤
        (2*exponent*lower^(-discrepancyBound)/slope)*rho*ratio^depth) := by
  have exponent_positive : 0 < exponent := by linarith
  have bases := centered_prefix_base_bounds positive less_one verticalDepth tailDepth depth digits tail_small vertical_small
  have first_bounds := centeredNewtonFirstCoefficient_bounds exponent_greater_one.le positive tailDepth depth
    bases.1 (by linarith [bases.2.1, pow_nonneg positive.le (tailDepth+depth)])
  have resonance := centered_resonance_two_sided_bound lower_positive ratio_lower less_one.le discrepancy_nonnegative phase_bound
  have second_bounds := centeredNewtonSecondCoefficient_bounds exponent_greater_one.le positive
    horizontalDepth verticalDepth tailDepth depth (Real.rpow_pos_of_pos lower_positive discrepancyBound).le
    resonance.1 resonance.2 bases.2.2.1
    (by linarith [bases.2.2.2, pow_nonneg positive.le (verticalDepth+tailDepth+depth)])
  have first_lower := mul_le_mul_of_nonneg_left tail_lower
    (show 0 ≤ exponent*(1/2 : ℝ)^(exponent-1) by positivity)
  have first_lower' := mul_le_mul_of_nonneg_right first_lower (pow_nonneg positive.le depth)
  have first_upper := mul_le_mul_of_nonneg_left tail_upper exponent_positive.le
  have first_upper' := mul_le_mul_of_nonneg_right first_upper (pow_nonneg positive.le depth)
  have second_lower := mul_le_mul_of_nonneg_left tail_lower
    (show 0 ≤ exponent*lower^discrepancyBound*(1/2 : ℝ)^(exponent-1) by positivity)
  have second_lower' := mul_le_mul_of_nonneg_right second_lower (pow_nonneg positive.le depth)
  have second_upper := mul_le_mul_of_nonneg_left tail_upper
    (show 0 ≤ exponent*lower^(-discrepancyBound) by positivity)
  have second_upper' := mul_le_mul_of_nonneg_right second_upper (pow_nonneg positive.le depth)
  have first_divided := newton_coefficient_div_slope_bounds (by positivity)
    (first_lower'.trans first_bounds.1) (first_bounds.2.trans first_upper')
    slope_positive derivative_negative derivative_bound
  have second_divided := newton_coefficient_div_slope_bounds (by positivity)
    (second_lower'.trans second_bounds.1) (second_bounds.2.trans second_upper')
    slope_positive derivative_negative derivative_bound
  simp only [FrozenNewtonKernel.firstScale, FrozenNewtonKernel.secondScale, centeredFrozenNewton]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · convert first_divided.1 using 1 <;>
      first | rfl | (simp only [zeroPrefixDigits]; field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring) | (field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring)
  · convert first_divided.2 using 1 <;>
      first | rfl | (simp only [zeroPrefixDigits]; field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring) | (field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring)
  · convert second_divided.1 using 1 <;>
      first | rfl | (simp only [zeroPrefixDigits]; field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring) | (field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring)
  · convert second_divided.2 using 1 <;>
      first | rfl | (simp only [zeroPrefixDigits]; field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring) | (field_simp [derivativeBound_positive.ne', slope_positive.ne'] <;> ring)

end LambdaCantor.AE
