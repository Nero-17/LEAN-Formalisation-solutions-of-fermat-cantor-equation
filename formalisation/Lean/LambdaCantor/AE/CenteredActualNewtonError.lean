import LambdaCantor.AE.CenteredPrefixTaylor
import LambdaCantor.AE.CenteredFullSecond
import LambdaCantor.AE.NewtonRemainder
import LambdaCantor.AE.NewtonQuadraticScale

noncomputable section
open Set Filter
open scoped Topology

namespace LambdaCantor.AE

theorem centeredHorizontalFactor_positive_of_tail_small
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (tailDepth : ℕ) (digits : ℕ → Bool) (tail_small : ratio^tailDepth ≤ 1/2) :
    0 < centeredHorizontalFactor tailDepth digits ratio := by
  have nonnegative := address_nonnegative positive.le less_one digits
  have product := mul_nonneg (pow_nonneg positive.le tailDepth) nonnegative
  unfold centeredHorizontalFactor
  linarith

/-- The derivative used by the actual frozen kernel is the derivative of
the complete zero-tail normalized residual, including its constant term. -/
theorem centeredPrefixBaseline_hasDerivAt (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth < 1) :
    HasDerivAt
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index))
      (centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth
        (pairedZeroPrefixDigits depth digits) ratio) ratio := by
  have actual := centeredNormalizedResidual_first_actual exponent horizontalDepth verticalDepth tailDepth
    (pairedZeroPrefixDigits depth digits) positive less_one
    (centeredHorizontalFactor_positive_of_tail_small positive less_one tailDepth _ tail_small) vertical_small
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Ioo (0 : ℝ) 1 from ⟨positive, less_one⟩)]
    with parameter membership
  exact centeredPrefixBaseline_eq_normalized exponent horizontalDepth verticalDepth tailDepth depth digits
    membership.1 membership.2

/-- Full same-address Newton error for the genuine centered kernel. The
mixed and complete second derivative bounds are on the displayed actual
residuals; the frozen-tail error and all first derivatives are derived here. -/
theorem centered_actual_newton_quadratic_error
    {exponent freezing root upper rho normalizedBound mixedBound secondBound displacementConstant slope : ℝ}
    (exponent_greater_one : 1 < exponent)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (digits : ℕ → Bool × Bool)
    (rho_nonnegative : 0 ≤ rho) (normalized_nonnegative : 0 ≤ normalizedBound)
    (mixed_nonnegative : 0 ≤ mixedBound) (second_nonnegative : 0 ≤ secondBound)
    (displacement_constant_nonnegative : 0 ≤ displacementConstant) (slope_positive : 0 < slope)
    (vertical_large : 1 ≤ verticalDepth)
    (band : ∀ parameter ∈ uIcc freezing root, 0 < parameter ∧ parameter < 1 ∧
      parameter^tailDepth ≤ 1/2 ∧ parameter^verticalDepth ≤ 1/2)
    (freezing_upper : freezing ≤ upper) (tail_rho : freezing^tailDepth ≤ 2*rho)
    (normalized_bound : (verticalDepth : ℝ)^2*
      (freezing^(-exponent*(horizontalDepth : ℝ))*(freezing^verticalDepth)^2) ≤ normalizedBound)
    (root_zero : centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits root = 0)
    (slope_lower : slope ≤ |deriv
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index)) freezing|)
    (second_bound : ∀ parameter ∈ uIcc freezing root,
      |centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth
        (pairedZeroPrefixDigits depth digits) parameter| ≤ secondBound)
    (mixed_bound : ∀ parameter ∈ uIcc freezing root,
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) parameter -
        deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth
          (pairedZeroPrefixDigits depth digits)) parameter| ≤
        mixedBound*rho*(((tailDepth+depth+1 : ℕ) : ℝ))*upper^depth)
    (displacement_bound : |root-freezing| ≤ displacementConstant*rho*upper^depth) :
    |root - (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth
      (fun index => digits index) freezing).value (fun index => digits (index+depth))| ≤
      ((4*(exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*(1+normalizedBound) +
        mixedBound*displacementConstant + secondBound*displacementConstant^2)/slope)*
          rho^2*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^depth)^2 := by
  have freezing_band := band freezing left_mem_uIcc
  have upper_positive := freezing_band.1.trans_le freezing_upper
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := by linarith
  have actual_first : ∀ parameter ∈ uIcc freezing root,
      HasDerivAt (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits)
        (centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth digits parameter) parameter := by
    intro parameter membership
    have conditions := band parameter membership
    exact centeredNormalizedResidual_first_actual exponent horizontalDepth verticalDepth tailDepth digits
      conditions.1 conditions.2.1
      (centeredHorizontalFactor_positive_of_tail_small conditions.1 conditions.2.1 tailDepth _ conditions.2.2.1)
      (by linarith [conditions.2.2.2])
  have baseline_first : ∀ parameter ∈ uIcc freezing root,
      HasDerivAt
        (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index))
        (centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth
          (pairedZeroPrefixDigits depth digits) parameter) parameter := by
    intro parameter membership
    have conditions := band parameter membership
    exact centeredPrefixBaseline_hasDerivAt exponent horizontalDepth verticalDepth tailDepth depth digits
      conditions.1 conditions.2.1 conditions.2.2.1 (by linarith [conditions.2.2.2])
  have baseline_second : ∀ parameter ∈ uIcc freezing root,
      HasDerivAt
        (centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits))
        (centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth
          (pairedZeroPrefixDigits depth digits) parameter) parameter := by
    intro parameter membership
    have conditions := band parameter membership
    exact centeredNormalizedResidual_second_actual exponent horizontalDepth verticalDepth tailDepth
      (pairedZeroPrefixDigits depth digits) conditions.1 conditions.2.1
      (centeredHorizontalFactor_positive_of_tail_small conditions.1 conditions.2.1 tailDepth _ conditions.2.2.1)
      (by linarith [conditions.2.2.2])
  have slope_identity := (baseline_first freezing left_mem_uIcc).deriv
  have slope_bound : slope ≤ |centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth
      (pairedZeroPrefixDigits depth digits) freezing| := by simpa only [slope_identity] using slope_lower
  have slope_nonzero : centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth
      (pairedZeroPrefixDigits depth digits) freezing ≠ 0 := abs_pos.mp (slope_positive.trans_le slope_bound)
  have tail_remainder := centered_frozen_actual_tail_rho_remainder exponent_greater_one
    freezing_band.1 freezing_band.2.1 freezing_upper rho_nonnegative horizontalDepth verticalDepth tailDepth depth digits
    vertical_large freezing_band.2.2.1 freezing_band.2.2.2 tail_rho normalized_bound
  have error := complete_newton_error_bound
    (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits)
    (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth (fun index => digits index))
    (centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits))
    (centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits))
    root_zero slope_nonzero second_nonnegative (fun parameter membership => (actual_first parameter membership).differentiableAt)
    baseline_first baseline_second second_bound (fun parameter membership => by
      have conditions := band parameter membership
      have first := centeredNormalizedResidual_first_actual exponent horizontalDepth verticalDepth tailDepth
        (pairedZeroPrefixDigits depth digits) conditions.1 conditions.2.1
        (centeredHorizontalFactor_positive_of_tail_small conditions.1 conditions.2.1 tailDepth _ conditions.2.2.1)
        (by linarith [conditions.2.2.2])
      simpa only [first.deriv] using mixed_bound parameter membership) tail_remainder
  have scale := newton_quadratic_scale_bound
    (tailBound := 4*(exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*(1+normalizedBound))
    (by positivity) mixed_nonnegative second_nonnegative displacement_constant_nonnegative rho_nonnegative
    (pow_nonneg upper_positive.le depth)
    (show (1 : ℝ) ≤ ((tailDepth+depth+1 : ℕ) : ℝ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))
    (abs_nonneg _) displacement_bound slope_positive slope_bound
  simpa only [FrozenNewtonKernel.value, centeredFrozenNewton, slope_identity] using error.trans scale

end LambdaCantor.AE
