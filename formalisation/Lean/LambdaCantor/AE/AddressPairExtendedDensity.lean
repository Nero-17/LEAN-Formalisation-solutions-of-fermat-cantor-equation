import LambdaCantor.AE.AddressPairBandImage
import LambdaCantor.AE.AddressPairNearBand

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace LambdaCantor.AE

/-- Extend the inverse density by zero outside the actual image. This avoids
using the arbitrary value of invFunOn at points having no inverse. -/
def addressPairExtendedDensity (first second third fourth : ℕ → Bool)
    (lower upper band : ℝ) (parameterCutoff valueCutoff : ℝ → ℝ) : ℝ → ℝ :=
  (addressPairDifference first second third fourth ''
    addressPairBand first second third fourth lower upper band).indicator
      (addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff)

/-- Compact support of the parameter cutoff and support of the value cutoff
strictly inside the value band keep the extended density's support away
from every boundary point of the actual image. No assumption that the
value cutoff is supported inside the image is required. -/
theorem addressPairExtendedDensity_support
    (first second third fourth : ℕ → Bool) {lower upper band : ℝ}
    (parameterCutoff valueCutoff : ℝ → ℝ)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hcompact : HasCompactSupport parameterCutoff)
    (hparameterSupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hvalueSupport : tsupport valueCutoff ⊆ Ioo (-band) band) :
    HasCompactSupport (addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) ∧
    tsupport (addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) ⊆
      addressPairDifference first second third fourth ''
        addressPairBand first second third fourth lower upper band := by
  have hcontinuous : ContinuousOn (addressPairDifference first second third fourth)
      (tsupport parameterCutoff) := fun ratio hratio =>
    (hdifferentiable ratio (hparameterSupport hratio)).continuousAt.continuousWithinAt
  have hcompactContainer : IsCompact
      ((addressPairDifference first second third fourth '' tsupport parameterCutoff) ∩
        tsupport valueCutoff) :=
    (hcompact.image_of_continuousOn hcontinuous).inter_right (isClosed_tsupport valueCutoff)
  have hsupport : Function.support (addressPairExtendedDensity first second third fourth
      lower upper band parameterCutoff valueCutoff) ⊆
      (addressPairDifference first second third fourth '' tsupport parameterCutoff) ∩
        tsupport valueCutoff := by
    intro value hnonzero
    change addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff value ≠ 0 at hnonzero
    have hvalue : value ∈ addressPairDifference first second third fourth ''
        addressPairBand first second third fourth lower upper band := by
      by_contra houtside
      exact hnonzero (by simp [addressPairExtendedDensity, houtside])
    have hdensity : addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff value ≠ 0 := by
      simpa only [addressPairExtendedDensity, indicator_of_mem hvalue] using hnonzero
    have hparameter : parameterCutoff
        (addressPairInverse first second third fourth lower upper band value) ≠ 0 := by
      intro hzero
      apply hdensity
      simp only [addressPairInverseDensity, hzero, zero_mul, zero_div]
    have hcutoff : valueCutoff value ≠ 0 := by
      intro hzero
      exact hdensity (addressPairInverseDensity_zero_outside first second third fourth
        lower upper band parameterCutoff valueCutoff hzero)
    exact ⟨⟨_, subset_tsupport parameterCutoff hparameter,
      (addressPairInverse_mem_and_right_inverse first second third fourth lower upper band hvalue).2⟩,
      subset_tsupport valueCutoff hcutoff⟩
  have hclosedSupport : tsupport (addressPairExtendedDensity first second third fourth
      lower upper band parameterCutoff valueCutoff) ⊆
      (addressPairDifference first second third fourth '' tsupport parameterCutoff) ∩
        tsupport valueCutoff := closure_minimal hsupport hcompactContainer.isClosed
  refine ⟨hcompactContainer.of_isClosed_subset (isClosed_tsupport _) hclosedSupport, ?_⟩
  intro value hvalue
  obtain ⟨⟨ratio, hratio, hequality⟩, hcutoff⟩ := hclosedSupport hvalue
  refine ⟨ratio, ⟨hparameterSupport hratio, ?_⟩, hequality⟩
  change addressPairDifference first second third fourth ratio ∈ Ioo (-band) band
  rw [hequality]
  exact hvalueSupport hcutoff

/-- Every point outside the actual image, including its boundary, has a
neighbourhood on which the zero-extended density is identically zero. -/
theorem hasDerivAt_addressPairExtendedDensity_outside
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff : ℝ → ℝ)
    (hsupport : tsupport (addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) ⊆ addressPairDifference first second third fourth ''
        addressPairBand first second third fourth lower upper band)
    {value : ℝ} (houtside : value ∉ addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band) :
    HasDerivAt (addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) 0 value := by
  have hnotSupport : value ∉ tsupport (addressPairExtendedDensity first second third fourth
      lower upper band parameterCutoff valueCutoff) := fun h => houtside (hsupport h)
  apply (hasDerivAt_const value (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [(isClosed_tsupport (addressPairExtendedDensity first second third fourth
    lower upper band parameterCutoff valueCutoff)).isOpen_compl.mem_nhds hnotSupport] with nearby hnearby
  exact image_eq_zero_of_notMem_tsupport hnearby

theorem lipschitzWith_addressPairExtendedDensity
    (first second third fourth : ℕ → Bool) {lower upper band : ℝ}
    (parameterCutoff valueCutoff : ℝ → ℝ) (constant : ℝ≥0)
    (hopen : IsOpen (addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band))
    (hsupport : tsupport (addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) ⊆ addressPairDifference first second third fourth ''
        addressPairBand first second third fourth lower upper band)
    (hlocal : ∀ value ∈ addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band,
      DifferentiableAt ℝ (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value ∧
      |deriv (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value| ≤ constant) :
    LipschitzWith constant (addressPairExtendedDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) := by
  have hglobal : ∀ value,
      DifferentiableAt ℝ (addressPairExtendedDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value ∧
      |deriv (addressPairExtendedDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value| ≤ constant := by
    intro value
    by_cases hvalue : value ∈ addressPairDifference first second third fourth ''
        addressPairBand first second third fourth lower upper band
    · have heventually : addressPairExtendedDensity first second third fourth lower upper band
          parameterCutoff valueCutoff =ᶠ[𝓝 value]
          addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff := by
        filter_upwards [hopen.mem_nhds hvalue] with nearby hnearby
        exact indicator_of_mem hnearby _
      have hderiv := (hlocal value hvalue).1.hasDerivAt.congr_of_eventuallyEq heventually
      exact ⟨hderiv.differentiableAt, by rw [hderiv.deriv]; exact (hlocal value hvalue).2⟩
    · have hzero := hasDerivAt_addressPairExtendedDensity_outside first second third fourth
        lower upper band parameterCutoff valueCutoff hsupport hvalue
      exact ⟨hzero.differentiableAt, by rw [hzero.deriv, abs_zero]; exact constant.coe_nonneg⟩
  apply lipschitzWith_of_nnnorm_deriv_le (fun value => (hglobal value).1)
  intro value
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, Real.norm_eq_abs] using (hglobal value).2

end LambdaCantor.AE
