import LambdaCantor.Last.RationalLastParameterEntrance
import LambdaCantor.Last.RationalLastNormalizationExchange
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem joint_strict_derivative_with_given_spatial_derivative
    (family : ℝ → (ℝ × ℝ) → ℝ) (ratio : ℝ) (point : ℝ × ℝ)
    (smooth : ContDiffAt ℝ 2 (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2) (ratio, point))
    (linear : (ℝ × ℝ) →L[ℝ] ℝ)
    (derivative : HasStrictFDerivAt (family ratio) linear point) :
    ∃ jointLinear : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2) jointLinear (ratio, point) ∧
      ∀ increment : ℝ × ℝ, jointLinear (0, increment) = linear increment := by
  let jointLinear := fderiv ℝ (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2) (ratio, point)
  have joint_derivative : HasStrictFDerivAt
      (fun value : ℝ × (ℝ × ℝ) => family value.1 value.2) jointLinear (ratio, point) :=
    smooth.hasStrictFDerivAt (by norm_num)
  have inclusion_derivative : HasStrictFDerivAt (fun value : ℝ × ℝ => (ratio, value))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) point :=
    (hasStrictFDerivAt_const (𝕜 := ℝ) ratio point).prodMk (hasStrictFDerivAt_id point)
  have partial_derivative := joint_derivative.comp point inclusion_derivative
  have equal := partial_derivative.hasFDerivAt.unique derivative.hasFDerivAt
  refine ⟨jointLinear, joint_derivative, ?_⟩
  intro increment
  have evaluation := congrArg (fun derivative : (ℝ × ℝ) →L[ℝ] ℝ => derivative increment) equal
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] using evaluation

theorem contDiff_scalarWordMap_joint (word : List Bool) :
    ContDiff ℝ 2 (fun value : ℝ × ℝ => scalarWordMap value.1 word value.2) := by
  induction word with
  | nil => exact contDiff_snd
  | cons digit rest induction =>
    cases digit
    · simpa only [scalarWordMap, Bool.false_eq_true, if_false, zero_add] using
        contDiff_fst.mul induction
    · simpa only [scalarWordMap, if_true] using
        (contDiff_const.sub contDiff_fst).add (contDiff_fst.mul induction)

theorem continuous_normalizedFermatPrefix_joint {exponent : ℝ} (exponent_nonnegative : 0 ≤ exponent)
    (firstWord secondWord : List Bool) (height : ℝ) :
    Continuous (fun value : ℝ × (ℝ × ℝ) =>
      normalizedFermatPrefix exponent value.1 firstWord secondWord height value.2) := by
  have first_coordinate : Continuous (fun value : ℝ × (ℝ × ℝ) =>
      scalarWordMap value.1 firstWord value.2.1) := (contDiff_scalarWordMap_joint firstWord).continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have second_coordinate : Continuous (fun value : ℝ × (ℝ × ℝ) =>
      scalarWordMap value.1 secondWord value.2.2) := (contDiff_scalarWordMap_joint secondWord).continuous.comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact (((first_coordinate.rpow_const (fun _ => Or.inr exponent_nonnegative)).add
    (second_coordinate.rpow_const (fun _ => Or.inr exponent_nonnegative))).sub continuous_const).div_const height

theorem contDiffAt_normalizedFermatPrefix_joint {exponent ratio height : ℝ}
    (firstWord secondWord : List Bool) (point : ℝ × ℝ)
    (first_positive : 0 < scalarWordMap ratio firstWord point.1)
    (second_positive : 0 < scalarWordMap ratio secondWord point.2) :
    ContDiffAt ℝ 2 (fun value : ℝ × (ℝ × ℝ) =>
      normalizedFermatPrefix exponent value.1 firstWord secondWord height value.2) (ratio, point) := by
  have first_coordinate : ContDiff ℝ 2 (fun value : ℝ × (ℝ × ℝ) =>
      scalarWordMap value.1 firstWord value.2.1) := (contDiff_scalarWordMap_joint firstWord).comp
    (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  have second_coordinate : ContDiff ℝ 2 (fun value : ℝ × (ℝ × ℝ) =>
      scalarWordMap value.1 secondWord value.2.2) := (contDiff_scalarWordMap_joint secondWord).comp
    (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))
  have first_power := (first_coordinate.contDiffAt (x := (ratio, point))).rpow_const_of_ne
    (p := exponent) first_positive.ne'
  have second_power := (second_coordinate.contDiffAt (x := (ratio, point))).rpow_const_of_ne
    (p := exponent) second_positive.ne'
  simpa only [normalizedFermatPrefix, div_eq_mul_inv] using
    ((first_power.add second_power).sub (contDiffAt_const :
      ContDiffAt ℝ 2 (fun _ : ℝ × (ℝ × ℝ) => (1 : ℝ)) (ratio, point))).mul
      (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × (ℝ × ℝ) => height⁻¹) (ratio, point))

/-- Normalization uses a fixed nonzero height. Consequently the actual
Fermat family is continuous in the contraction even away from the chosen
rectangle and is jointly C² at its positive selected point. -/
theorem normalizedFermatPrefix_joint_derivative {exponent ratio height slope : ℝ}
    (firstWord secondWord : List Bool) (point : ℝ × ℝ)
    (first_positive : 0 < scalarWordMap ratio firstWord point.1)
    (second_positive : 0 < scalarWordMap ratio secondWord point.2)
    (derivative : HasStrictFDerivAt (normalizedFermatPrefix exponent ratio firstWord secondWord height)
      (positiveLinearContinuous slope) point) :
    ∃ jointLinear : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ,
      HasStrictFDerivAt (fun value : ℝ × (ℝ × ℝ) =>
        normalizedFermatPrefix exponent value.1 firstWord secondWord height value.2) jointLinear (ratio, point) ∧
      ∀ increment : ℝ × ℝ, jointLinear (0, increment) = positiveLinearContinuous slope increment :=
  joint_strict_derivative_with_given_spatial_derivative
    (fun perturbed => normalizedFermatPrefix exponent perturbed firstWord secondWord height) ratio point
    (contDiffAt_normalizedFermatPrefix_joint firstWord secondWord point first_positive second_positive)
    (positiveLinearContinuous slope) derivative

end LambdaCantor.Last
