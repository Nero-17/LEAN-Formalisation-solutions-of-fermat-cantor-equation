import LambdaCantor.AE.CenteredPrefixComparison
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set
namespace LambdaCantor.AE

/-- Quantitative lower and upper bounds for the power map on a positive unit
subinterval. These estimates are used on actual centred cylinder coordinates. -/
theorem centered_power_difference_bounds {exponent minimum first second : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (minimum_positive : 0 < minimum)
    (first_mem : first ∈ Icc minimum 1) (second_mem : second ∈ Icc minimum 1) :
    exponent*minimum^(exponent-1)*|first-second| ≤ |first^exponent-second^exponent| ∧
      |first^exponent-second^exponent| ≤ exponent*|first-second| := by
  have derivative : ∀ point ∈ Icc minimum 1,
      HasDerivAt (fun parameter : ℝ => parameter^exponent)
        (exponent*point^(exponent-1)) point := by
    intro point point_mem
    simpa using (hasDerivAt_id point).rpow_const (p := exponent)
      (Or.inl (ne_of_gt (minimum_positive.trans_le point_mem.1)))
  have continuous : ContinuousOn (fun point : ℝ => point^exponent) (Icc minimum 1) :=
    fun point point_mem => (derivative point point_mem).continuousAt.continuousWithinAt
  have differentiable : DifferentiableOn ℝ (fun point : ℝ => point^exponent) (interior (Icc minimum 1)) := by
    intro point point_mem
    exact (derivative point (interior_subset point_mem)).differentiableAt.differentiableWithinAt
  have lower_derivative : ∀ point ∈ interior (Icc minimum 1),
      exponent*minimum^(exponent-1) ≤ deriv (fun parameter : ℝ => parameter^exponent) point := by
    intro point point_mem
    rw [(derivative point (interior_subset point_mem)).deriv]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow minimum_positive.le (interior_subset point_mem).1 (by linarith)) (by linarith)
  have lower_change := (convex_Icc minimum 1).mul_sub_le_image_sub_of_le_deriv
    continuous differentiable lower_derivative
  constructor
  · rcases le_total first second with ordered | ordered
    · have change := lower_change first first_mem second second_mem ordered
      rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
      have absolute := neg_le_abs (first^exponent-second^exponent)
      nlinarith
    · have change := lower_change second second_mem first first_mem ordered
      rw [abs_of_nonneg (sub_nonneg.mpr ordered)]
      have absolute := le_abs_self (first^exponent-second^exponent)
      nlinarith
  · have bound := (convex_Icc minimum 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := exponent)
      (fun point point_mem => (derivative point point_mem).hasDerivWithinAt)
      (by
        intro point point_mem
        have point_positive := minimum_positive.trans_le point_mem.1
        have exponent_nonnegative : 0 ≤ exponent := (by norm_num : (0 : ℝ) ≤ 1).trans exponent_ge_one
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg exponent_nonnegative (Real.rpow_nonneg point_positive.le _))]
        have power_bound := Real.rpow_le_one point_positive.le point_mem.2
          (show 0 ≤ exponent-1 by linarith)
        exact mul_le_of_le_one_right exponent_nonnegative power_bound)
      second_mem first_mem
    simpa only [Real.norm_eq_abs] using bound

/-- Holding the second address fixed, the actual residual changes by exactly
the horizontal power difference; the entire Taylor remainder cancels. -/
theorem centered_residual_first_tail_difference
    (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (first other second : ℕ → Bool) (ratio : ℝ) :
    centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth
      (fun index => (first index, second index)) ratio -
    centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth
      (fun index => (other index, second index)) ratio =
      centeredHorizontalFactor tailDepth first ratio^exponent -
        centeredHorizontalFactor tailDepth other ratio^exponent := by
  simp only [centeredNormalizedResidual]
  ring

/-- Actual first-tail expansion lower bound, including the vanishing cylinder
scale ratio^tailDepth. -/
theorem centered_residual_first_tail_lower
    {exponent ratio : ℝ} (exponent_ge_one : 1 ≤ exponent)
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ) (small_power : ratio^tailDepth ≤ 1/2)
    (first other second : ℕ → Bool) :
    (exponent*(1/2:ℝ)^(exponent-1))*ratio^tailDepth*|address ratio first-address ratio other| ≤
      |centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth
        (fun index => (first index, second index)) ratio -
       centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth
        (fun index => (other index, second index)) ratio| := by
  have factor_bounds : ∀ digits : ℕ → Bool,
      centeredHorizontalFactor tailDepth digits ratio ∈ Icc (1/2:ℝ) 1 := by
    intro digits
    have address_bounds : address ratio digits ∈ Icc (0:ℝ) 1 := ⟨address_nonnegative ratio_positive.le ratio_less_one digits,
      address_le_one ratio_positive.le ratio_less_one digits⟩
    unfold centeredHorizontalFactor
    have power_nonnegative := pow_nonneg ratio_positive.le tailDepth
    constructor <;> nlinarith [mul_nonneg power_nonnegative address_bounds.1,
      mul_le_mul_of_nonneg_left address_bounds.2 power_nonnegative]
  have bound := (centered_power_difference_bounds exponent_ge_one (by norm_num : (0:ℝ)<1/2)
    (factor_bounds first) (factor_bounds other)).1
  rw [centered_residual_first_tail_difference]
  have difference : centeredHorizontalFactor tailDepth first ratio - centeredHorizontalFactor tailDepth other ratio =
      ratio^tailDepth*(address ratio first-address ratio other) := by
    unfold centeredHorizontalFactor
    ring
  rw [difference, abs_mul, abs_of_nonneg (pow_nonneg ratio_positive.le tailDepth)] at bound
  simpa only [mul_assoc] using bound

end LambdaCantor.AE

