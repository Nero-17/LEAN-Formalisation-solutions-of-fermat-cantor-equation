import LambdaCantor.AE.CenteredPrefixLipschitz

noncomputable section
open Set
namespace LambdaCantor.AE

theorem centered_residual_shared_prefix_bound
    {exponent ratio upper coefficientBound : ℝ} (exponent_ge_one : 1 ≤ exponent)
    (positive : 0 < ratio) (less_one : ratio < 1) (ratio_upper : ratio ≤ upper)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2)
    (coefficient_bound : exponent*ratio^((verticalDepth:ℝ)-exponent*horizontalDepth) ≤ coefficientBound)
    (first second : ℕ → Bool × Bool)
    (agreement : ∀ position < depth, first position = second position) :
    |centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth first ratio -
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth second ratio| ≤
      (exponent+coefficientBound)*ratio^tailDepth*upper^depth := by
  have first_close := First.PrefixSlopes.address_close_of_prefix positive.le less_one
    (fun position before => congrArg Prod.fst (agreement position before))
  have second_close := First.PrefixSlopes.address_close_of_prefix positive.le less_one
    (fun position before => congrArg Prod.snd (agreement position before))
  have power_upper := pow_le_pow_left₀ positive.le ratio_upper depth
  have bound := centered_residual_tail_lipschitz exponent_ge_one positive less_one
    horizontalDepth verticalDepth tailDepth tail_small vertical_small first second
  have first_bound := mul_le_mul_of_nonneg_left (first_close.trans power_upper)
    (show 0 ≤ exponent*ratio^tailDepth by positivity)
  have coefficient_nonnegative : 0 ≤ exponent*ratio^((verticalDepth:ℝ)-exponent*horizontalDepth) := by positivity
  have second_bound := mul_le_mul
    (mul_le_mul_of_nonneg_right coefficient_bound (pow_nonneg positive.le tailDepth))
    (second_close.trans power_upper) (abs_nonneg _)
    (mul_nonneg (coefficient_nonnegative.trans coefficient_bound) (pow_nonneg positive.le tailDepth))
  nlinarith [bound, first_bound, second_bound]

/-- Prefix displacement on the actual rho scale. The tail Lipschitz estimate
is derived above from the actual normalized residual, not postulated here. -/
theorem centered_root_shared_prefix_displacement
    {exponent lower upper rho slope coefficientBound : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (lower_positive : 0 < lower) (upper_less_one : upper < 1)
    (rho_positive : 0 < rho) (slope_positive : 0 < slope)
    (coefficient_nonnegative : 0 ≤ coefficientBound)
    (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (root : (ℕ → Bool × Bool) → ℝ)
    (root_mem : ∀ digits, root digits ∈ Icc lower upper)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (root_power_upper : ∀ digits, (root digits)^tailDepth ≤ 2*rho)
    (root_power_small : ∀ digits, (root digits)^tailDepth ≤ 1/2)
    (vertical_power_small : ∀ digits, (root digits)^verticalDepth ≤ 1/2)
    (coefficient_bound : ∀ digits, exponent*(root digits)^((verticalDepth:ℝ)-exponent*horizontalDepth) ≤ coefficientBound)
    (continuous : ∀ digits, ContinuousOn
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (Icc lower upper))
    (differentiable : ∀ digits, DifferentiableOn ℝ
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (Ioo lower upper))
    (derivative_bound : ∀ digits ratio, ratio ∈ Ioo lower upper →
      deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio ≤ -slope)
    (first second : ℕ → Bool × Bool)
    (agreement : ∀ position < depth, first position = second position) :
    |root first-root second| ≤ (2*(exponent+coefficientBound)/slope)*rho*upper^depth := by
  have common_bound := centered_residual_shared_prefix_bound exponent_ge_one
    (lower_positive.trans_le (root_mem second).1) ((root_mem second).2.trans_lt upper_less_one)
    (root_mem second).2 horizontalDepth verticalDepth tailDepth depth
    (root_power_small second) (vertical_power_small second) (coefficient_bound second) first second agreement
  have upper_positive : 0 < upper := (lower_positive.trans_le (root_mem second).1).trans_le (root_mem second).2
  have scaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (root_power_upper second) (by linarith : 0 ≤ exponent+coefficientBound))
    (pow_nonneg upper_positive.le depth)
  have bound := centered_root_pair_displacement exponent horizontalDepth verticalDepth tailDepth root
    slope_positive root_mem root_zero continuous differentiable derivative_bound first second
    (common_bound.trans scaled)
  convert bound using 1 <;> ring

end LambdaCantor.AE
