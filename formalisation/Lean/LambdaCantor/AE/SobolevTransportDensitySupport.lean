import LambdaCantor.AE.SobolevTransportAssembly
import LambdaCantor.AE.ScaledConvolutionMeasure

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

theorem scaledConvolutionProbability_compl_support {ratio firstScale secondScale : ℝ}
    (hratio : 0 ≤ ratio) (hratioOne : ratio < 1)
    (hfirst : 0 ≤ firstScale) (hsecond : 0 ≤ secondScale) :
    scaledConvolutionProbability ratio firstScale secondScale
      (Icc (-(firstScale + secondScale)) (firstScale + secondScale))ᶜ = 0 := by
  rw [scaledConvolutionProbability,
    Measure.map_apply (measurable_scaled_sum_addresses ratio firstScale secondScale)
      measurableSet_Icc.compl]
  have hempty : (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
      firstScale * address ratio digits.1 + secondScale * address ratio digits.2) ⁻¹'
      (Icc (-(firstScale + secondScale)) (firstScale + secondScale))ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro digits hnot
    apply hnot
    have hfirstNonnegative := mul_nonneg hfirst (address_nonnegative hratio hratioOne digits.1)
    have hsecondNonnegative := mul_nonneg hsecond (address_nonnegative hratio hratioOne digits.2)
    have hfirstBound := mul_le_mul_of_nonneg_left (address_le_one hratio hratioOne digits.1) hfirst
    have hsecondBound := mul_le_mul_of_nonneg_left (address_le_one hratio hratioOne digits.2) hsecond
    constructor <;> nlinarith
  rw [hempty, measure_empty]

/-- Restricting a density to the known support of its measure changes it only
on a null set. This supplies the pointwise support required by mollification. -/
theorem indicator_density_ae_eq_of_measure_support {density : ℝ → ℝ} {support : Set ℝ}
    (hsupport : MeasurableSet support) (hdensity : AEStronglyMeasurable density volume)
    (hnonnegative : ∀ᵐ value : ℝ, 0 ≤ density value)
    (hmass : volume.withDensity (fun value => ENNReal.ofReal (density value)) supportᶜ = 0) :
    support.indicator density =ᵐ[volume] density := by
  rw [withDensity_apply _ hsupport.compl] at hmass
  have hzero := (lintegral_eq_zero_iff'
    hdensity.aemeasurable.ennreal_ofReal.restrict).mp hmass
  have hzeroOutside : ∀ᵐ value : ℝ, value ∈ supportᶜ →
      ENNReal.ofReal (density value) = 0 :=
    (ae_restrict_iff' hsupport.compl).mp hzero
  filter_upwards [hnonnegative, hzeroOutside] with value hnonnegativeValue hzeroValue
  by_cases hinside : value ∈ support
  · simp only [Set.indicator_of_mem hinside]
  · rw [Set.indicator_of_notMem hinside]
    have hnonpositive := ENNReal.ofReal_eq_zero.mp (hzeroValue hinside)
    linarith

theorem integral_probability_density_eq_one (probability : Measure ℝ)
    [IsProbabilityMeasure probability] {density : ℝ → ℝ}
    (hdensity : Integrable density) (hnonnegative : ∀ᵐ value : ℝ, 0 ≤ density value)
    (hmeasure : probability = volume.withDensity (fun value => ENNReal.ofReal (density value))) :
    (∫ value : ℝ, density value) = 1 := by
  have hmass := congrArg (fun measure : Measure ℝ => measure univ) hmeasure
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hdensity hnonnegative] at hmass
  have hnonnegativeIntegral := integral_nonneg_of_ae hnonnegative
  have := congrArg ENNReal.toReal hmass
  simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal hnonnegativeIntegral] using this.symm

theorem exists_supported_density_of_measure_support (probability : Measure ℝ)
    {density : ℝ → ℝ} {radius : ℝ}
    (hdensity : Integrable density) (hLp : MemLp density 2 volume)
    (hnonnegative : ∀ᵐ value : ℝ, 0 ≤ density value)
    (hmeasure : probability = volume.withDensity (fun value => ENNReal.ofReal (density value)))
    (hmass : probability (Icc (-radius) radius)ᶜ = 0) :
    ∃ supportedDensity : ℝ → ℝ,
      Integrable supportedDensity ∧ MemLp supportedDensity 2 volume ∧
      (∀ᵐ value : ℝ, 0 ≤ supportedDensity value) ∧
      Function.support supportedDensity ⊆ Icc (-radius) radius ∧
      probability = volume.withDensity (fun value => ENNReal.ofReal (supportedDensity value)) ∧
      supportedDensity =ᵐ[volume] density ∧
      𝓕 (fun value => (supportedDensity value : ℂ)) = 𝓕 (fun value => (density value : ℂ)) := by
  rw [hmeasure] at hmass
  have hequal := indicator_density_ae_eq_of_measure_support measurableSet_Icc
    hdensity.aestronglyMeasurable hnonnegative hmass
  refine ⟨(Icc (-radius) radius).indicator density,
    hdensity.congr hequal.symm, (memLp_congr_ae hequal).mpr hLp, ?_, ?_, ?_, hequal, ?_⟩
  · filter_upwards [hequal, hnonnegative] with value hequalValue hnonnegativeValue
    rwa [hequalValue]
  · intro value hvalue
    by_contra houtside
    exact hvalue (Set.indicator_of_notMem houtside density)
  · rw [hmeasure]
    exact withDensity_congr_ae (hequal.symm.fun_comp ENNReal.ofReal)
  · funext frequency
    rw [Real.fourier_real_eq, Real.fourier_real_eq]
    apply integral_congr_ae
    filter_upwards [hequal] with value hequalValue
    rw [hequalValue]

theorem probability_density_L1_distance_le_two
    {first second : ℝ → ℝ} (hfirst : Integrable first) (hsecond : Integrable second)
    (hfirstNonnegative : ∀ᵐ value : ℝ, 0 ≤ first value)
    (hsecondNonnegative : ∀ᵐ value : ℝ, 0 ≤ second value)
    (hfirstMass : (∫ value : ℝ, first value) = 1)
    (hsecondMass : (∫ value : ℝ, second value) = 1) :
    (∫ value : ℝ, |first value - second value|) ≤ 2 := by
  calc
    _ ≤ ∫ value : ℝ, first value + second value := by
      apply integral_mono_ae (hfirst.sub hsecond).abs (hfirst.add hsecond)
      filter_upwards [hfirstNonnegative, hsecondNonnegative] with value hfirstValue hsecondValue
      change |first value - second value| ≤ first value + second value
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ = 2 := by rw [integral_add hfirst hsecond, hfirstMass, hsecondMass]; norm_num

end LambdaCantor.AE
