import LambdaCantor.AE.CenteredCoefficient
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

theorem centered_horizontal_power_drop_bound {exponent ratio : ℝ}
    (hexponent : 1 ≤ exponent) (hpositive : 0 < ratio) (hless : ratio < 1)
    (tailDepth : ℕ) (digits : ℕ → Bool) :
    |(centeredHorizontalFactor tailDepth digits ratio) ^ exponent - 1| ≤
      exponent * ratio ^ tailDepth := by
  have haddress := cantorSet_subset_unitInterval hpositive.le hless
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩)
  have hpower := pow_nonneg hpositive.le tailDepth
  have hpowerUpper := pow_le_one₀ hpositive.le hless.le (n := tailDepth)
  have hfactor : 0 ≤ centeredHorizontalFactor tailDepth digits ratio ∧
      centeredHorizontalFactor tailDepth digits ratio ≤ 1 := by
    unfold centeredHorizontalFactor
    constructor <;> nlinarith [mul_nonneg hpower haddress.1,
      mul_le_mul_of_nonneg_left haddress.2 hpower]
  have hbernoulli := one_add_mul_self_le_rpow_one_add
    (show -1 ≤ centeredHorizontalFactor tailDepth digits ratio - 1 by linarith [hfactor.1]) hexponent
  have hupper := Real.rpow_le_one hfactor.1 hfactor.2 (by linarith : 0 ≤ exponent)
  have hdrop := centeredHorizontalFactor_bounds tailDepth digits hpositive hless
  rw [abs_of_nonpos (by linarith : (centeredHorizontalFactor tailDepth digits ratio) ^ exponent - 1 ≤ 0)]
  have hlower := (abs_le.mp hdrop).1
  have hweighted := mul_le_mul_of_nonneg_left hlower (by linarith : 0 ≤ exponent)
  have hequality : 1 + (centeredHorizontalFactor tailDepth digits ratio - 1) =
      centeredHorizontalFactor tailDepth digits ratio := by ring
  rw [hequality] at hbernoulli
  linarith

/-- The center value is controlled on the same scale as the root window.
The coefficient and remainder hypotheses are quantitative errors proved
separately for the actual irrational depths. -/
theorem centered_center_residual_bound {exponent center coefficientBound remainderBound : ℝ}
    (hexponent : 1 ≤ exponent) (hcenter : 0 < center) (hless : center < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    (hcoefficient : |exponent * center ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) - 1| ≤
      coefficientBound * center ^ tailDepth)
    (hcoefficientUpper : exponent * center ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) ≤ 2)
    (hremainder : |centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth
      (fun index => (digits index).2) center| ≤ remainderBound * center ^ tailDepth) :
    |centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits center| ≤
      (exponent + coefficientBound + 2 + remainderBound) * center ^ tailDepth := by
  have hpower := centered_horizontal_power_drop_bound hexponent hcenter hless tailDepth
    (fun index => (digits index).1)
  have htail := centeredTailFactor_bounds tailDepth (fun index => (digits index).2) hcenter hless
  have hcoefficientNonnegative : 0 ≤ exponent * center ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hcenter.le _)
  have htailProduct : |exponent * center ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) *
      (1 - centeredTailFactor tailDepth (fun index => (digits index).2) center)| ≤ 2 * center ^ tailDepth := by
    rw [abs_mul, abs_of_nonneg hcoefficientNonnegative, abs_sub_comm]
    exact mul_le_mul hcoefficientUpper htail (abs_nonneg _) (by norm_num)
  have hidentity : centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits center =
      ((centeredHorizontalFactor tailDepth (fun index => (digits index).1) center) ^ exponent - 1) +
      (1 - exponent * center ^ ((verticalDepth : ℝ) - exponent * horizontalDepth)) +
      exponent * center ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) *
        (1 - centeredTailFactor tailDepth (fun index => (digits index).2) center) +
      centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth
        (fun index => (digits index).2) center := by
    unfold centeredNormalizedResidual
    ring
  rw [hidentity]
  apply (abs_add_le _ _).trans
  apply (add_le_add ((abs_add_le _ _).trans
    (add_le_add (abs_add_le _ _) (le_refl _))) (le_refl _)).trans
  rw [abs_sub_comm 1]
  linarith

theorem centered_actual_remainder_linear_scale_bound
    {exponent center upper target taylorBound : ℝ}
    (hexponent : 1 < exponent) (hcenter : 0 < center) (hupper : center ≤ upper) (hless : upper < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ) (hdepth : 1 ≤ verticalDepth) (digits : ℕ → Bool)
    (hsmall : center ^ verticalDepth ≤ 1 / 2)
    (hphase : |(verticalDepth : ℝ) - exponent * horizontalDepth - target| ≤ (center ^ tailDepth) ^ 2)
    (hdecay : (verticalDepth : ℝ) ^ 2 * upper ^ verticalDepth ≤ (center ^ tailDepth) ^ 3)
    (htaylorBound : exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) ≤ taylorBound) :
    |centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth digits center| ≤
      (taylorBound * center ^ (-(|target| + 1))) * center ^ tailDepth := by
  have hcenterLess := hupper.trans_lt hless
  have hexponentPositive : 0 < exponent := by linarith
  have hexponentMinus : 0 < exponent - 1 := by linarith
  have htaylorNonnegative : 0 ≤ taylorBound := le_trans (by positivity) htaylorBound
  have hscaleUpper : center ^ tailDepth ≤ 1 := pow_le_one₀ hcenter.le hcenterLess.le
  have hscaleSquare : (center ^ tailDepth) ^ 2 ≤ 1 :=
    pow_le_one₀ (pow_nonneg hcenter.le _) hscaleUpper
  have hscaleCube : (center ^ tailDepth) ^ 3 ≤ center ^ tailDepth := by
    simpa only [pow_one] using pow_le_pow_of_le_one
      (pow_nonneg hcenter.le tailDepth) hscaleUpper (by omega : 1 ≤ 3)
  have hnormalized := centered_normalized_quadratic_decay hcenter le_rfl hupper hless
    horizontalDepth verticalDepth hphase hscaleSquare hdecay
  have hdepthReal : (1 : ℝ) ≤ verticalDepth := by exact_mod_cast hdepth
  have hsquare : (1 : ℝ) ≤ (verticalDepth : ℝ) ^ 2 := by nlinarith
  have hfactor : 0 ≤ center ^ (-exponent * (horizontalDepth : ℝ)) * (center ^ verticalDepth) ^ 2 := by positivity
  have hremainder := centered_actual_remainder_bound hexponent hcenter hcenterLess
    horizontalDepth verticalDepth tailDepth digits hsmall
  change |center ^ (-exponent * (horizontalDepth : ℝ)) *
    centeredTaylorRemainder exponent (centeredAddressDisplacement verticalDepth tailDepth digits center)| ≤ _
  calc
    _ ≤ taylorBound * (center ^ (-exponent * (horizontalDepth : ℝ)) * (center ^ verticalDepth) ^ 2) :=
      hremainder.trans (mul_le_mul_of_nonneg_right htaylorBound hfactor)
    _ ≤ taylorBound * ((verticalDepth : ℝ) ^ 2 *
        (center ^ (-exponent * (horizontalDepth : ℝ)) * (center ^ verticalDepth) ^ 2)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hfactor hsquare) htaylorNonnegative
    _ ≤ taylorBound * (center ^ (-(|target| + 1)) * (center ^ tailDepth) ^ 3) :=
      mul_le_mul_of_nonneg_left hnormalized htaylorNonnegative
    _ = (taylorBound * center ^ (-(|target| + 1))) * (center ^ tailDepth) ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaleCube (by positivity)

theorem centered_center_residual_eventual_bound {exponent center upper : ℝ}
    (hexponent : 1 < exponent) (hcenter : 0 < center) (hupper : center ≤ upper) (hless : upper < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (hdepth : ∀ index, index ≤ verticalDepth index) (htwo : ∀ index, 2 ≤ verticalDepth index)
    (hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index +
      Real.log exponent / Real.log center| ≤ (center ^ index) ^ 2)
    (hdecay : ∀ index, (verticalDepth index : ℝ) ^ 2 * upper ^ verticalDepth index ≤ (center ^ index) ^ 3) :
    ∃ errorBound : ℝ, 0 ≤ errorBound ∧ ∀ᶠ index : ℕ in Filter.atTop,
      ∀ digits : ℕ → Bool × Bool,
        |centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits center| ≤
          errorBound * center ^ index := by
  let taylorBound := exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))
  let coefficientBound := Real.exp 1 * |Real.log center|
  let remainderBound := taylorBound * center ^ (-(|Real.log exponent / Real.log center| + 1))
  have hcenterLess := hupper.trans_lt hless
  have hexponentPositive : 0 < exponent := by linarith
  have hexponentMinus : 0 < exponent - 1 := by linarith
  have htaylorNonnegative : 0 ≤ taylorBound := by dsimp [taylorBound]; positivity
  have hcoefficientNonnegative : 0 ≤ coefficientBound := by dsimp [coefficientBound]; positivity
  have hremainderNonnegative : 0 ≤ remainderBound := by dsimp [remainderBound]; positivity
  refine ⟨exponent + coefficientBound + 2 + remainderBound, by positivity, ?_⟩
  have hscale := tendsto_pow_atTop_nhds_zero_of_lt_one hcenter.le hcenterLess
  have hlogSmall : ∀ᶠ index : ℕ in Filter.atTop, |Real.log center| * (center ^ index) ^ 2 < 1 := by
    have hlimit : Tendsto (fun index => |Real.log center| * (center ^ index) ^ 2) atTop (𝓝 0) := by
      simpa using (hscale.pow 2).const_mul |Real.log center|
    exact hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hcoefficientSmall : ∀ᶠ index : ℕ in Filter.atTop, coefficientBound * (center ^ index) ^ 2 < 1 := by
    have hlimit : Tendsto (fun index => coefficientBound * (center ^ index) ^ 2) atTop (𝓝 0) := by
      simpa using (hscale.pow 2).const_mul coefficientBound
    exact hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpowerSmall : ∀ᶠ index : ℕ in Filter.atTop, upper ^ index < (1 / 2 : ℝ) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hcenter.le.trans hupper) hless).eventually
      (gt_mem_nhds (by norm_num))
  filter_upwards [hlogSmall, hcoefficientSmall, hpowerSmall] with index hlogSmall hcoefficientSmall hpowerSmall
  intro digits
  have hscaleUpper : center ^ index ≤ 1 := pow_le_one₀ hcenter.le hcenterLess.le
  have hscaleSquare : (center ^ index) ^ 2 ≤ center ^ index := by
    simpa only [pow_one] using pow_le_pow_of_le_one
      (pow_nonneg hcenter.le index) hscaleUpper (by omega : 1 ≤ 2)
  have hcoefficientError := centered_coefficient_near_one hexponentPositive hcenter hcenterLess
    (hphase index) hlogSmall.le
  have hcoefficientError' : |exponent * center ^ ((verticalDepth index : ℝ) - exponent * horizontalDepth index) - 1| ≤
      coefficientBound * (center ^ index) ^ 2 := by
    simpa only [coefficientBound, mul_assoc] using hcoefficientError
  have hcoefficientUpper : exponent * center ^ ((verticalDepth index : ℝ) - exponent * horizontalDepth index) ≤ 2 := by
    have hupperError := (abs_le.mp hcoefficientError').2
    linarith
  have hsmall : center ^ verticalDepth index ≤ 1 / 2 :=
    ((pow_le_pow_left₀ hcenter.le hupper _).trans
      (pow_le_pow_of_le_one (hcenter.le.trans hupper) hless.le (hdepth index))).trans hpowerSmall.le
  have hphase' : |(verticalDepth index : ℝ) - exponent * horizontalDepth index -
      (-Real.log exponent / Real.log center)| ≤ (center ^ index) ^ 2 := by
    simpa only [neg_div, sub_neg_eq_add] using hphase index
  have hremainder := centered_actual_remainder_linear_scale_bound hexponent hcenter hupper hless
    (horizontalDepth index) (verticalDepth index) index (by have := htwo index; omega)
    (fun position => (digits position).2) hsmall hphase' (hdecay index) (le_refl taylorBound)
  apply centered_center_residual_bound hexponent.le hcenter hcenterLess
    (horizontalDepth index) (verticalDepth index) index digits
    (hcoefficientError'.trans (mul_le_mul_of_nonneg_left hscaleSquare hcoefficientNonnegative)) hcoefficientUpper
  simpa only [neg_div, abs_neg, remainderBound] using hremainder

end LambdaCantor.AE
