import LambdaCantor.AE.CenteredPrefixes
import LambdaCantor.AE.CenteredResidual

noncomputable section
open Set

namespace LambdaCantor.AE
open First.Roots

theorem centered_cylinderResidual_identity (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    cylinderResidual exponent (centeredLeftPrefix horizontalDepth) (centeredRightPrefix verticalDepth)
      (horizontalDepth+tailDepth) (verticalDepth+tailDepth) digits ratio =
      ratio^(exponent*horizontalDepth) *
        centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio := by
  have coordinates := centered_prefix_coordinates ratio horizontalDepth verticalDepth tailDepth
    (fun index => (digits index).1) (fun index => (digits index).2)
  have first_coordinate := congrArg Prod.fst coordinates
  have second_coordinate := congrArg Prod.snd coordinates
  simp only [Prod.fst, Prod.snd] at first_coordinate second_coordinate
  unfold cylinderResidual
  rw [first_coordinate, second_coordinate,
    centeredNormalizedResidual_actual exponent horizontalDepth verticalDepth tailDepth digits positive less_one]
  field_simp [(Real.rpow_pos_of_pos positive (exponent*horizontalDepth)).ne']

theorem centered_cylinderResidual_derivative_at_zero (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (differentiable : DifferentiableAt ℝ
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio)
    (zero : centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio = 0) :
    deriv (cylinderResidual exponent (centeredLeftPrefix horizontalDepth) (centeredRightPrefix verticalDepth)
      (horizontalDepth+tailDepth) (verticalDepth+tailDepth) digits) ratio =
      ratio^(exponent*horizontalDepth) *
        deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio := by
  have scale := (hasDerivAt_id' ratio).rpow_const (p := exponent*(horizontalDepth : ℝ)) (Or.inl positive.ne')
  have identity :
      cylinderResidual exponent (centeredLeftPrefix horizontalDepth) (centeredRightPrefix verticalDepth)
        (horizontalDepth+tailDepth) (verticalDepth+tailDepth) digits =ᶠ[nhds ratio]
      (fun parameter => parameter^(exponent*horizontalDepth) *
        centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits parameter) := by
    filter_upwards [Ioo_mem_nhds positive less_one] with parameter membership
    exact centered_cylinderResidual_identity exponent horizontalDepth verticalDepth tailDepth digits membership.1 membership.2
  rw [identity.deriv_eq]
  simpa only [zero, mul_zero, zero_add] using (scale.fun_mul differentiable.hasDerivAt).deriv

/-- The actual centered full cylinders satisfy the geometric root-fibre
interface. Only their already constructed roots and transverse normalized
derivatives are needed; no root-fibre conclusion is assumed. -/
def centeredRootFibreData {exponent lower upper slope : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_quarter : 1/4 < lower)
    (upper_half : upper < 1/2) (ordered : lower ≤ upper)
    (horizontalDepth verticalDepth tailDepth : ℕ)
    (vertical_positive : 1 ≤ verticalDepth) (tail_positive : 1 ≤ tailDepth)
    (root : (ℕ → Bool × Bool) → ℝ)
    (root_mem : ∀ digits, root digits ∈ Icc lower upper)
    (unique_root : ∀ digits ratio, ratio ∈ Icc lower upper →
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio = 0 ↔ ratio = root digits))
    (slope_positive : 0 < slope)
    (differentiable : ∀ digits, DifferentiableAt ℝ
      (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (root digits))
    (negative_derivative : ∀ digits,
      deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) (root digits) ≤ -slope) :
    RootFibreData exponent where
  exponent_gt_one := exponent_greater_one
  lower := lower
  upper := upper
  lower_gt_quarter := lower_quarter
  upper_lt_half := upper_half
  ordered := ordered
  leftWord := centeredLeftPrefix horizontalDepth
  rightWord := centeredRightPrefix verticalDepth
  leftLength := horizontalDepth+tailDepth
  rightLength := verticalDepth+tailDepth
  root := root
  root_in_band := root_mem
  left_positive := by
    intro digits ratio membership
    have positive : 0 < ratio := (by linarith : 0 < lower).trans_le membership.1
    have less_one : ratio < 1 := by linarith [membership.2]
    have address_nonnegative := address_nonnegative positive.le less_one (fun index => (digits index).1)
    rw [cylinderCoordinate, centeredLeftPrefix_value]
    exact add_pos_of_pos_of_nonneg
      (mul_pos (pow_pos positive _) (sub_pos.mpr (pow_lt_one₀ positive.le less_one (by omega))))
      (mul_nonneg (pow_nonneg positive.le _) address_nonnegative)
  right_positive := by
    intro digits ratio membership
    have positive : 0 < ratio := (by linarith : 0 < lower).trans_le membership.1
    have less_one : ratio < 1 := by linarith [membership.2]
    have address_nonnegative := address_nonnegative positive.le less_one (fun index => (digits index).2)
    rw [cylinderCoordinate, centeredRightPrefix_value]
    exact add_pos_of_pos_of_nonneg
      (sub_pos.mpr (pow_lt_one₀ positive.le less_one (by omega)))
      (mul_nonneg (pow_nonneg positive.le _) address_nonnegative)
  unique_root := by
    intro digits ratio membership
    have positive : 0 < ratio := (by linarith : 0 < lower).trans_le membership.1
    have less_one : ratio < 1 := by linarith [membership.2]
    rw [centered_cylinderResidual_identity exponent horizontalDepth verticalDepth tailDepth digits positive less_one,
      mul_eq_zero, or_iff_right (Real.rpow_pos_of_pos positive (exponent*horizontalDepth)).ne']
    exact unique_root digits ratio membership
  derivative_lower_bound := slope*lower^(exponent*horizontalDepth)
  derivative_lower_bound_positive :=
    mul_pos slope_positive (Real.rpow_pos_of_pos (by linarith : 0 < lower) _)
  transverse := by
    intro digits
    have lower_positive : 0 < lower := by linarith
    have positive := lower_positive.trans_le (root_mem digits).1
    have less_one : root digits < 1 := by linarith [(root_mem digits).2]
    rw [centered_cylinderResidual_derivative_at_zero exponent horizontalDepth verticalDepth tailDepth digits
      positive less_one (differentiable digits) ((unique_root digits _ (root_mem digits)).mpr rfl),
      abs_mul, abs_of_pos (Real.rpow_pos_of_pos positive _),
      abs_of_neg (by linarith [negative_derivative digits])]
    have power_lower := Real.rpow_le_rpow lower_positive.le (root_mem digits).1
      (show 0 ≤ exponent*(horizontalDepth : ℝ) from
        mul_nonneg (by linarith : 0 ≤ exponent) (Nat.cast_nonneg horizontalDepth))
    calc
      _ ≤ slope*(root digits)^(exponent*horizontalDepth) :=
        mul_le_mul_of_nonneg_left power_lower slope_positive.le
      _ ≤ _ := by nlinarith [Real.rpow_pos_of_pos positive (exponent*horizontalDepth), negative_derivative digits]

end LambdaCantor.AE
