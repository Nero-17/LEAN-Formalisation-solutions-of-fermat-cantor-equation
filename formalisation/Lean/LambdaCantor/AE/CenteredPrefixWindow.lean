import LambdaCantor.AE.CenteredPrefixSeparation
import LambdaCantor.AE.CenteredPrefixDisplacement

noncomputable section
open Set
namespace LambdaCantor.AE

theorem centered_prefix_displacement_constant_positive {exponent coefficientBound slope : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (coefficient_nonnegative : 0 ≤ coefficientBound)
    (slope_positive : 0 < slope) : 0 < 2*(exponent+coefficientBound)/slope := by
  have exponent_positive : 0 < exponent := by linarith
  positivity

theorem centered_smallBall_constant_positive {exponent lower upper derivativeBound dimension : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (lower_positive : 0 < lower)
    (upper_half : upper < 1/2) (derivative_positive : 0 < derivativeBound) :
    0 < ((4*derivativeBound)/((exponent*(1/2:ℝ)^(exponent-1))*(1-2*upper)*lower))^dimension := by
  have exponent_positive : 0 < exponent := by linarith
  have gap_positive : 0 < 1-2*upper := by linarith
  apply Real.rpow_pos_of_pos
  positivity

/-- Separate the shrinking root window from the fixed Cantor contraction band.
Only derivatives on the root window are required. -/
theorem centered_root_first_coordinate_separation_on_window
    {exponent lower upper windowLower windowUpper rho derivativeBound : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (lower_positive : 0 < lower) (upper_half : upper < 1/2)
    (window_lower : lower ≤ windowLower) (window_upper : windowUpper ≤ upper)
    (rho_positive : 0 < rho) (derivative_positive : 0 < derivativeBound)
    (horizontalDepth verticalDepth tailDepth : ℕ)
    (root : (ℕ → Bool × Bool) → ℝ)
    (root_mem : ∀ digits, root digits ∈ Icc windowLower windowUpper)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (root_power_lower : ∀ digits, rho/2 ≤ (root digits)^tailDepth)
    (root_power_small : ∀ digits, (root digits)^tailDepth ≤ 1/2)
    (differentiable : ∀ digits ratio, ratio ∈ Icc windowLower windowUpper →
      DifferentiableAt ℝ (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio)
    (derivative_bound : ∀ digits ratio, ratio ∈ Icc windowLower windowUpper →
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio| ≤ derivativeBound)
    (second : ℕ → Bool) (depth : ℕ) (first other : ℕ → Bool)
    (different : ∃ position < depth, first position ≠ other position) :
    ((exponent*(1/2:ℝ)^(exponent-1))*(rho/2)*(1-2*upper)/derivativeBound)*lower^depth ≤
      |root (fun index => (first index, second index))-root (fun index => (other index, second index))| := by
  have narrow_bound := centered_root_first_coordinate_separation exponent_ge_one
    (lower_positive.trans_le window_lower) (window_upper.trans_lt upper_half) rho_positive derivative_positive
    horizontalDepth verticalDepth tailDepth root root_mem root_zero root_power_lower root_power_small
    differentiable derivative_bound second depth first other different
  apply le_trans _ narrow_bound
  have coefficient_nonnegative : 0 ≤ (exponent*(1/2:ℝ)^(exponent-1))*(rho/2) := by positivity
  have coefficient_bound := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show 1-2*upper ≤ 1-2*windowUpper by linarith) coefficient_nonnegative)
    derivative_positive.le
  exact mul_le_mul coefficient_bound (pow_le_pow_left₀ lower_positive.le window_lower depth)
    (pow_nonneg lower_positive.le depth) (by
      have : 0 ≤ 1-2*windowUpper := by linarith
      positivity)

/-- Shared-prefix displacement with derivatives confined to the shrinking root
window and a fixed upper contraction for the depth factor. -/
theorem centered_root_shared_prefix_displacement_on_window
    {exponent lower upper windowLower windowUpper rho slope coefficientBound : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (lower_positive : 0 < lower) (upper_less_one : upper < 1)
    (window_lower : lower ≤ windowLower) (window_upper : windowUpper ≤ upper)
    (rho_positive : 0 < rho) (slope_positive : 0 < slope) (coefficient_nonnegative : 0 ≤ coefficientBound)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (root : (ℕ → Bool × Bool) → ℝ)
    (root_mem : ∀ digits, root digits ∈ Icc windowLower windowUpper)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (root_power_upper : ∀ digits, (root digits)^tailDepth ≤ 2*rho)
    (root_power_small : ∀ digits, (root digits)^tailDepth ≤ 1/2)
    (vertical_power_small : ∀ digits, (root digits)^verticalDepth ≤ 1/2)
    (coefficient_bound : ∀ digits, exponent*(root digits)^((verticalDepth:ℝ)-exponent*horizontalDepth) ≤ coefficientBound)
    (continuous : ∀ digits, ContinuousOn
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (Icc windowLower windowUpper))
    (differentiable : ∀ digits, DifferentiableOn ℝ
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (Ioo windowLower windowUpper))
    (derivative_bound : ∀ digits ratio, ratio ∈ Ioo windowLower windowUpper →
      deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio ≤ -slope)
    (first second : ℕ → Bool × Bool) (agreement : ∀ position < depth, first position = second position) :
    |root first-root second| ≤ (2*(exponent+coefficientBound)/slope)*rho*upper^depth := by
  have narrow_bound := centered_root_shared_prefix_displacement exponent_ge_one
    (lower_positive.trans_le window_lower) (window_upper.trans_lt upper_less_one) rho_positive slope_positive
    coefficient_nonnegative horizontalDepth verticalDepth tailDepth depth root root_mem root_zero
    root_power_upper root_power_small vertical_power_small coefficient_bound continuous differentiable
    derivative_bound first second agreement
  apply narrow_bound.trans
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [(root_mem second).1, (root_mem second).2]) window_upper depth)
  positivity

end LambdaCantor.AE

