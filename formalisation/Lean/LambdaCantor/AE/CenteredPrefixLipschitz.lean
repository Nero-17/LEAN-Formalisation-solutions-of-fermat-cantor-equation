import LambdaCantor.AE.CenteredPrefixTailSlope
import LambdaCantor.First.PrefixCylinder

noncomputable section
open Set
namespace LambdaCantor.AE

theorem centered_abs_add_sub_add_le (first second third fourth : ℝ) :
    |(first+second)-(third+fourth)| ≤ |first-third|+|second-fourth| := by
  convert abs_add_le (first-third) (second-fourth) using 1 <;> congr 1 <;> ring

/-- Unit-interval power Lipschitz bound without introducing a fixed positive
lower endpoint into the application interface. -/
theorem centered_power_unit_lipschitz {exponent first second : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (first_positive : 0 < first) (first_le : first ≤ 1)
    (second_positive : 0 < second) (second_le : second ≤ 1) :
    |first^exponent-second^exponent| ≤ exponent*|first-second| :=
  (centered_power_difference_bounds exponent_ge_one (lt_min first_positive second_positive)
    ⟨min_le_left _ _, first_le⟩ ⟨min_le_right _ _, second_le⟩).2

/-- Exact separated horizontal/vertical formula for the normalized residual. -/
theorem centered_residual_scalar_formula
    (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool × Bool) {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio =
      (1-ratio^tailDepth+ratio^tailDepth*address ratio (fun index => (digits index).1))^exponent +
      ((1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*address ratio (fun index => (digits index).2))^exponent-1) /
        ratio^(exponent*horizontalDepth) := by
  rw [centeredNormalizedResidual_actual exponent horizontalDepth verticalDepth tailDepth digits positive less_one]
  have horizontal_nonnegative : 0 ≤ 1-ratio^tailDepth+ratio^tailDepth*address ratio (fun index => (digits index).1) := by
    have power_le := pow_le_one₀ positive.le less_one.le (n := tailDepth)
    have address_nonnegative := address_nonnegative positive.le less_one (fun index => (digits index).1)
    have difference_nonnegative : 0 ≤ 1-ratio^tailDepth := sub_nonneg.mpr power_le
    positivity
  have horizontal_power :
      (ratio^horizontalDepth*(1-ratio^tailDepth+ratio^tailDepth*address ratio (fun index => (digits index).1)))^exponent =
      ratio^(exponent*horizontalDepth)*(1-ratio^tailDepth+ratio^tailDepth*address ratio (fun index => (digits index).1))^exponent := by
    rw [Real.mul_rpow (pow_nonneg positive.le _) horizontal_nonnegative,
      ← Real.rpow_natCast_mul positive.le]
    congr 2
    ring
  simp only [centeredCylinder, Prod.fst, Prod.snd]
  rw [horizontal_power]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos positive (exponent*horizontalDepth))]
  <;> ring

/-- Common-parameter residual variation on actual paired addresses. Both tail
coordinates carry the same factor ratio^tailDepth after normalization. -/
theorem centered_residual_tail_lipschitz
    {exponent ratio : ℝ} (exponent_ge_one : 1 ≤ exponent)
    (positive : 0 < ratio) (less_one : ratio < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2)
    (first second : ℕ → Bool × Bool) :
    |centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth first ratio -
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth second ratio| ≤
      exponent*ratio^tailDepth * |address ratio (fun index => (first index).1)-address ratio (fun index => (second index).1)| +
      exponent*ratio^((verticalDepth:ℝ)-exponent*horizontalDepth)*ratio^tailDepth *
        |address ratio (fun index => (first index).2)-address ratio (fun index => (second index).2)| := by
  have horizontal_bounds : ∀ digits : ℕ → Bool,
      0 < 1-ratio^tailDepth+ratio^tailDepth*address ratio digits ∧
      1-ratio^tailDepth+ratio^tailDepth*address ratio digits ≤ 1 := by
    intro digits
    have lower := address_nonnegative positive.le less_one digits
    have upper := address_le_one positive.le less_one digits
    have power_nonnegative := pow_nonneg positive.le tailDepth
    constructor <;> nlinarith [mul_nonneg power_nonnegative lower, mul_le_mul_of_nonneg_left upper power_nonnegative]
  have vertical_bounds : ∀ digits : ℕ → Bool,
      0 < 1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*address ratio digits ∧
      1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*address ratio digits ≤ 1 := by
    intro digits
    have lower := address_nonnegative positive.le less_one digits
    have upper := address_le_one positive.le less_one digits
    have tail_le := pow_le_one₀ positive.le less_one.le (n := tailDepth)
    rw [pow_add]
    have tail_nonnegative := pow_nonneg positive.le tailDepth
    have vertical_nonnegative := pow_nonneg positive.le verticalDepth
    have product_le := mul_le_mul_of_nonneg_left (mul_le_one₀ tail_le lower upper) vertical_nonnegative
    constructor <;> nlinarith [mul_nonneg (mul_nonneg vertical_nonnegative tail_nonnegative) lower]
  have horizontal := centered_power_unit_lipschitz exponent_ge_one
    (horizontal_bounds (fun index => (first index).1)).1 (horizontal_bounds (fun index => (first index).1)).2
    (horizontal_bounds (fun index => (second index).1)).1 (horizontal_bounds (fun index => (second index).1)).2
  have vertical := centered_power_unit_lipschitz exponent_ge_one
    (vertical_bounds (fun index => (first index).2)).1 (vertical_bounds (fun index => (first index).2)).2
    (vertical_bounds (fun index => (second index).2)).1 (vertical_bounds (fun index => (second index).2)).2
  have horizontal_difference :
      (1-ratio^tailDepth+ratio^tailDepth*address ratio (fun index => (first index).1)) -
      (1-ratio^tailDepth+ratio^tailDepth*address ratio (fun index => (second index).1)) =
      ratio^tailDepth*(address ratio (fun index => (first index).1)-address ratio (fun index => (second index).1)) := by ring
  have vertical_difference :
      (1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*address ratio (fun index => (first index).2)) -
      (1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*address ratio (fun index => (second index).2)) =
      ratio^(verticalDepth+tailDepth)*(address ratio (fun index => (first index).2)-address ratio (fun index => (second index).2)) := by ring
  rw [horizontal_difference, abs_mul, abs_of_nonneg (pow_nonneg positive.le _)] at horizontal
  rw [vertical_difference, abs_mul, abs_of_nonneg (pow_nonneg positive.le _)] at vertical
  rw [centered_residual_scalar_formula exponent horizontalDepth verticalDepth tailDepth first positive less_one,
    centered_residual_scalar_formula exponent horizontalDepth verticalDepth tailDepth second positive less_one]
  have scale_positive := Real.rpow_pos_of_pos positive (exponent*horizontalDepth)
  have quotient : ratio^(verticalDepth+tailDepth)/ratio^(exponent*horizontalDepth) =
      ratio^((verticalDepth:ℝ)-exponent*horizontalDepth)*ratio^tailDepth := by
    rw [pow_add, Real.rpow_sub positive, Real.rpow_natCast]
    ring
  calc
    _ ≤ _ := centered_abs_add_sub_add_le _ _ _ _
    _ ≤ exponent*(ratio^tailDepth*|address ratio (fun index => (first index).1)-address ratio (fun index => (second index).1)|) +
      exponent*(ratio^(verticalDepth+tailDepth)*|address ratio (fun index => (first index).2)-address ratio (fun index => (second index).2)|)/ratio^(exponent*horizontalDepth) := by
      apply add_le_add horizontal
      rw [← sub_div, abs_div, abs_of_pos scale_positive]
      convert div_le_div_of_nonneg_right vertical scale_positive.le using 1 <;> congr 1 <;> ring
    _ = _ := by
      calc
        _ = exponent*ratio^tailDepth*|address ratio (fun index => (first index).1)-address ratio (fun index => (second index).1)| +
          exponent*(ratio^(verticalDepth+tailDepth)/ratio^(exponent*horizontalDepth))*|address ratio (fun index => (first index).2)-address ratio (fun index => (second index).2)| := by ring
        _ = _ := by rw [quotient]; ring

end LambdaCantor.AE


