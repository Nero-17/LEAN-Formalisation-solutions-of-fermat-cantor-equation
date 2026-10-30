import LambdaCantor.Last.RationalLastNormalizationScale
import LambdaCantor.Last.RationalLastNormalizationGeometry
import LambdaCantor.Last.RationalLastTangent
import LambdaCantor.Last.PositiveDerivatives
import LambdaCantor.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod

noncomputable section
namespace LambdaCantor.Last

def normalizedFermatPrefix (exponent ratio : ℝ) (firstWord secondWord : List Bool) (height : ℝ)
    (point : ℝ × ℝ) : ℝ :=
  ((scalarWordMap ratio firstWord point.1)^exponent+
    (scalarWordMap ratio secondWord point.2)^exponent-1)/height

theorem normalizedFermatPrefix_eq_affine (exponent ratio : ℝ)
    (firstWord secondWord : List Bool) (height : ℝ) :
    normalizedFermatPrefix exponent ratio firstWord secondWord height = fun point =>
      ((scalarWordMap ratio firstWord 0+ratio^firstWord.length*point.1)^exponent+
        (scalarWordMap ratio secondWord 0+ratio^secondWord.length*point.2)^exponent-1)/height := by
  funext point
  unfold normalizedFermatPrefix
  rw [scalarWordMap_affine ratio firstWord point.1, scalarWordMap_affine ratio secondWord point.2]

theorem normalizedFermatPrefix_contDiffAt {exponent ratio height : ℝ}
    (firstWord secondWord : List Bool) (point : ℝ × ℝ)
    (first_positive : 0 < scalarWordMap ratio firstWord point.1)
    (second_positive : 0 < scalarWordMap ratio secondWord point.2) :
    ContDiffAt ℝ 2 (normalizedFermatPrefix exponent ratio firstWord secondWord height) point := by
  have first_ne : scalarWordMap ratio firstWord 0+ratio^firstWord.length*point.1 ≠ 0 := by
    rw [← scalarWordMap_affine ratio firstWord point.1]
    exact first_positive.ne'
  have second_ne : scalarWordMap ratio secondWord 0+ratio^secondWord.length*point.2 ≠ 0 := by
    rw [← scalarWordMap_affine ratio secondWord point.2]
    exact second_positive.ne'
  have first_smooth : ContDiffAt ℝ 2
      (fun value : ℝ × ℝ => (scalarWordMap ratio firstWord 0+ratio^firstWord.length*value.1)^exponent) point :=
    (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_fst)).rpow_const_of_ne first_ne
  have second_smooth : ContDiffAt ℝ 2
      (fun value : ℝ × ℝ => (scalarWordMap ratio secondWord 0+ratio^secondWord.length*value.2)^exponent) point :=
    (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_snd)).rpow_const_of_ne second_ne
  rw [normalizedFermatPrefix_eq_affine]
  simpa only [div_eq_mul_inv] using
    ((first_smooth.add second_smooth).sub
      (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (1 : ℝ)) point)).mul
      (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => height⁻¹) point)

theorem normalizedFermatPrefix_hasStrictFDerivAt {exponent ratio height : ℝ}
    (firstWord secondWord : List Bool) (point : ℝ × ℝ)
    (first_positive : 0 < scalarWordMap ratio firstWord point.1)
    (second_positive : 0 < scalarWordMap ratio secondWord point.2) :
    HasStrictFDerivAt (normalizedFermatPrefix exponent ratio firstWord secondWord height)
      ((exponent*ratio^firstWord.length*(scalarWordMap ratio firstWord point.1)^(exponent-1)/height) •
          ContinuousLinearMap.fst ℝ ℝ ℝ+
        (exponent*ratio^secondWord.length*(scalarWordMap ratio secondWord point.2)^(exponent-1)/height) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) point := by
  have first_affine := ((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := point)).const_mul
    (ratio^firstWord.length)).const_add (scalarWordMap ratio firstWord 0)
  have second_affine := ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := point)).const_mul
    (ratio^secondWord.length)).const_add (scalarWordMap ratio secondWord 0)
  have first_power := first_affine.rpow_const (p := exponent) (Or.inl (show
      scalarWordMap ratio firstWord 0+ratio^firstWord.length*point.1 ≠ 0 by
    rw [← scalarWordMap_affine ratio firstWord point.1]
    exact first_positive.ne'))
  have second_power := second_affine.rpow_const (p := exponent) (Or.inl (show
      scalarWordMap ratio secondWord 0+ratio^secondWord.length*point.2 ≠ 0 by
    rw [← scalarWordMap_affine ratio secondWord point.2]
    exact second_positive.ne'))
  have derivative := ((first_power.add second_power).sub_const 1).const_mul height⁻¹
  refine (derivative.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)).congr_fderiv ?_
  · intro value
    unfold normalizedFermatPrefix
    rw [scalarWordMap_affine ratio firstWord value.1,
      scalarWordMap_affine ratio secondWord value.2]
    simp only [Pi.add_apply, div_eq_mul_inv]
    ring
  · apply ContinuousLinearMap.ext
    intro value
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, div_eq_mul_inv]
    rw [scalarWordMap_affine ratio firstWord point.1,
      scalarWordMap_affine ratio secondWord point.2]
    ring

theorem normalizedFermatPrefix_zero_mapsTo {exponent ratio height : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1) (height_nonzero : height ≠ 0)
    (firstWord secondWord : List Bool) :
    Set.MapsTo (anisotropicPrefixMap ratio firstWord secondWord)
      {point | point ∈ cantorDust ratio ∧ normalizedFermatPrefix exponent ratio firstWord secondWord height point = 0}
      (intersection exponent ratio) := by
  intro point membership
  have dust := anisotropicPrefixMap_mem_dust nonnegative less_one firstWord secondWord membership.1
  refine ⟨dust.1, dust.2, ?_⟩
  have zero := membership.2
  unfold normalizedFermatPrefix at zero
  have numerator_zero := (div_eq_zero_iff.mp zero).resolve_right height_nonzero
  change (scalarWordMap ratio firstWord point.1)^exponent+
    (scalarWordMap ratio secondWord point.2)^exponent = 1
  linarith

theorem normalizedFermatPrefix_isolated_pullback {exponent ratio height : ℝ}
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1) (height_nonzero : height ≠ 0)
    (firstWord secondWord : List Bool) (point : intersection exponent ratio)
    (preimage : {value | value ∈ cantorDust ratio ∧
      normalizedFermatPrefix exponent ratio firstWord secondWord height value = 0})
    (representation : anisotropicPrefixMap ratio firstWord secondWord preimage.val = point.val)
    (isolated : IsOpen ({point} : Set (intersection exponent ratio))) :
    IsOpen ({preimage} : Set {value | value ∈ cantorDust ratio ∧
      normalizedFermatPrefix exponent ratio firstWord secondWord height value = 0}) :=
  isolated_point_pullback (anisotropicPrefixMap ratio firstWord secondWord)
    (continuous_anisotropicPrefixMap ratio firstWord secondWord)
    (anisotropicPrefixMap_antilipschitz ratio_positive firstWord secondWord).injective
    (normalizedFermatPrefix_zero_mapsTo ratio_positive.le ratio_less_one height_nonzero firstWord secondWord)
    point preimage representation isolated

theorem fermatTangentRatio_eq_quotient_rpow {exponent : ℝ} {point : ℝ × ℝ}
    (first_positive : 0 < point.1) (second_positive : 0 < point.2) :
    fermatTangentRatio exponent point = (point.2/point.1)^(exponent-1) := by
  unfold fermatTangentRatio
  rw [Real.div_rpow second_positive.le first_positive.le]

/-- Every positive actual Fermat point has an actual anisotropic prefix
rectangle whose normalized function is C² and has strict derivative (1,r)
with 1≤r<1/λ. No normalization data is assumed. -/
theorem exists_actual_fermat_prefix_normalization {exponent ratio : ℝ}
    (exponent_gt_one : 1 < exponent) (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1)
    (point : intersection exponent ratio) (first_positive : 0 < point.val.1)
    (second_positive : 0 < point.val.2) :
    ∃ (firstWord secondWord : List Bool) (tail : ℝ × ℝ) (slope height : ℝ),
      tail ∈ cantorDust ratio ∧ anisotropicPrefixMap ratio firstWord secondWord tail = point.val ∧
      slope = ratio^secondWord.length/ratio^firstWord.length*fermatTangentRatio exponent point.val ∧
      1 ≤ slope ∧ slope < 1/ratio ∧ 0 < height ∧
      normalizedFermatPrefix exponent ratio firstWord secondWord height tail = 0 ∧
      ContDiffAt ℝ 2 (normalizedFermatPrefix exponent ratio firstWord secondWord height) tail ∧
      HasStrictFDerivAt (normalizedFermatPrefix exponent ratio firstWord secondWord height)
        (positiveLinearContinuous slope) tail := by
  have exponent_positive : 0 < exponent := by linarith
  have tangent_positive : 0 < fermatTangentRatio exponent point.val :=
    div_pos (Real.rpow_pos_of_pos second_positive _) (Real.rpow_pos_of_pos first_positive _)
  obtain ⟨firstDepth, secondDepth, slope_lower, slope_upper⟩ :=
    exists_natural_prefix_slope_normalization ratio_positive ratio_less_one tangent_positive
  obtain ⟨firstWord, first_length, firstTail, first_mem, first_representation⟩ :=
    exists_scalar_cylinder ratio_positive.le ratio_less_one firstDepth point.property.1
  obtain ⟨secondWord, second_length, secondTail, second_mem, second_representation⟩ :=
    exists_scalar_cylinder ratio_positive.le ratio_less_one secondDepth point.property.2.1
  let tail : ℝ × ℝ := (firstTail, secondTail)
  let slope := ratio^secondDepth/ratio^firstDepth*fermatTangentRatio exponent point.val
  let height := exponent*ratio^firstDepth*point.val.1^(exponent-1)
  have height_positive : 0 < height := mul_pos (mul_pos exponent_positive (pow_pos ratio_positive _))
    (Real.rpow_pos_of_pos first_positive _)
  have representation : anisotropicPrefixMap ratio firstWord secondWord tail = point.val :=
    Prod.ext first_representation.symm second_representation.symm
  have first_actual : 0 < scalarWordMap ratio firstWord tail.1 := by
    change 0 < scalarWordMap ratio firstWord firstTail
    rw [← first_representation]
    exact first_positive
  have second_actual : 0 < scalarWordMap ratio secondWord tail.2 := by
    change 0 < scalarWordMap ratio secondWord secondTail
    rw [← second_representation]
    exact second_positive
  refine ⟨firstWord, secondWord, tail, slope, height, ⟨first_mem, second_mem⟩, representation,
    by simp [slope, first_length, second_length], slope_lower, slope_upper, height_positive, ?_,
    normalizedFermatPrefix_contDiffAt firstWord secondWord tail first_actual second_actual, ?_⟩
  · unfold normalizedFermatPrefix
    change ((scalarWordMap ratio firstWord firstTail)^exponent+
      (scalarWordMap ratio secondWord secondTail)^exponent-1)/height = 0
    rw [← first_representation, ← second_representation, point.property.2.2]
    simp
  · have derivative := normalizedFermatPrefix_hasStrictFDerivAt (exponent := exponent) (height := height)
      firstWord secondWord tail first_actual second_actual
    change HasStrictFDerivAt (normalizedFermatPrefix exponent ratio firstWord secondWord height)
      ((exponent*ratio^firstWord.length*(scalarWordMap ratio firstWord firstTail)^(exponent-1)/height) •
          ContinuousLinearMap.fst ℝ ℝ ℝ+
        (exponent*ratio^secondWord.length*(scalarWordMap ratio secondWord secondTail)^(exponent-1)/height) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) tail at derivative
    rw [← first_representation, ← second_representation, first_length, second_length] at derivative
    apply derivative.congr_fderiv
    apply ContinuousLinearMap.ext
    intro value
    change (exponent*ratio^firstDepth*point.val.1^(exponent-1)/height)*value.1+
      (exponent*ratio^secondDepth*point.val.2^(exponent-1)/height)*value.2 = value.1+slope*value.2
    dsimp [slope, height, fermatTangentRatio]
    field_simp [exponent_positive.ne', (pow_pos ratio_positive firstDepth).ne',
      (Real.rpow_pos_of_pos first_positive (exponent-1)).ne']
    <;> ring

end LambdaCantor.Last
