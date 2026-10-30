import LambdaCantor.AE.SobolevTransportFourierMollifier
import LambdaCantor.AE.ClassicalSignedDensity

noncomputable section
open MeasureTheory Convolution Filter
open scoped FourierTransform ENNReal

namespace LambdaCantor.AE

def mollifyDensity (density : ℝ → ℝ) (scale : ℝ) : ℝ → ℝ :=
  density ⋆[ContinuousLinearMap.mul ℝ ℝ] transportMollifier scale

theorem integrable_mollifyDensity {density : ℝ → ℝ} (hdensity : Integrable density)
    {scale : ℝ} (hscale : 0 < scale) : Integrable (mollifyDensity density scale) :=
  hdensity.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (integrable_transportMollifier hscale)

theorem integrable_complex_of_real {density : ℝ → ℝ} (hdensity : Integrable density) :
    Integrable (fun value => (density value : ℂ)) :=
  hdensity.mono
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hdensity.aestronglyMeasurable)
    (Eventually.of_forall (fun value => by simp))

theorem fourier_mollifyDensity {density : ℝ → ℝ} (hdensity : Integrable density)
    {scale : ℝ} (hscale : 0 < scale) (frequency : ℝ) :
    𝓕 (fun value => (mollifyDensity density scale value : ℂ)) frequency =
      𝓕 (fun value => (density value : ℂ)) frequency *
        𝓕 (fun value => (transportMollifier scale value : ℂ)) frequency := by
  have hidentity : (fun value => (mollifyDensity density scale value : ℂ)) =
      (fun value => (density value : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun value => (transportMollifier scale value : ℂ)) := by
    funext value
    simp only [mollifyDensity, convolution_def, ContinuousLinearMap.mul_apply',
      ← integral_complex_ofReal, Complex.ofReal_mul]
  rw [hidentity]
  exact Real.fourier_mul_convolution_eq (integrable_complex_of_real hdensity)
    (integrable_complex_of_real (integrable_transportMollifier hscale)) frequency

theorem fourier_sub_integrable {first second : ℝ → ℂ}
    (hfirst : Integrable first) (hsecond : Integrable second) (frequency : ℝ) :
    𝓕 (fun value => first value - second value) frequency = 𝓕 first frequency - 𝓕 second frequency := by
  simp only [Real.fourier_eq, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff frequency).mpr hfirst)
    ((Real.fourierIntegral_convergent_iff frequency).mpr hsecond)

theorem fourier_mollification_error {density : ℝ → ℝ} (hdensity : Integrable density)
    {scale : ℝ} (hscale : 0 < scale) (frequency : ℝ) :
    𝓕 (fun value => ((density value - mollifyDensity density scale value : ℝ) : ℂ)) frequency =
      𝓕 (fun value => (density value : ℂ)) frequency *
        (1 - 𝓕 (fun value => (transportMollifier scale value : ℂ)) frequency) := by
  simp only [Complex.ofReal_sub]
  rw [fourier_sub_integrable (integrable_complex_of_real hdensity)
    (integrable_complex_of_real (integrable_mollifyDensity hdensity hscale)),
    fourier_mollifyDensity hdensity hscale]
  ring

theorem norm_fourier_mollification_error_sq_le {density : ℝ → ℝ}
    (hdensity : Integrable density) {scale regularity : ℝ} (hscale : 0 < scale)
    (hregularity : 0 ≤ regularity) (hregularityOne : regularity ≤ 1) (frequency : ℝ) :
    ‖𝓕 (fun value => ((density value - mollifyDensity density scale value : ℝ) : ℂ)) frequency‖ ^ 2 ≤
      ((2 * Real.pi + 2) * scale ^ regularity) ^ 2 *
        ((1 + |frequency| ^ (2 * regularity)) *
          ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2) := by
  rw [fourier_mollification_error hdensity hscale, norm_mul, norm_sub_rev]
  have hbound := transportMollifier_fourier_error_bound hscale hregularity hregularityOne frequency
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hmultiplied := mul_le_mul_of_nonneg_left hsquare
    (sq_nonneg ‖𝓕 (fun value => (density value : ℂ)) frequency‖)
  have hpower : (|frequency| ^ regularity) ^ 2 = |frequency| ^ (2 * regularity) := by
    rw [← Real.rpow_mul_natCast (abs_nonneg frequency) regularity 2]
    congr 1
    ring
  have hconstant : 0 ≤ ((2 * Real.pi + 2) * scale ^ regularity) ^ 2 := sq_nonneg _
  have hnorm : 0 ≤ ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2 := sq_nonneg _
  simp only [mul_pow, hpower] at hmultiplied
  nlinarith [mul_nonneg hconstant hnorm]

theorem mollification_error_memLp_and_energy_bound {density : ℝ → ℝ}
    (hdensity : Integrable density) {scale regularity : ℝ} (hscale : 0 < scale)
    (hregularity : 0 ≤ regularity) (hregularityOne : regularity ≤ 1)
    (henergy : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
      ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2)) < ⊤) :
    MemLp (fun value => density value - mollifyDensity density scale value) 2 volume ∧
      ENNReal.ofReal (∫ value : ℝ, |density value - mollifyDensity density scale value| ^ 2) ≤
        ENNReal.ofReal (((2 * Real.pi + 2) * scale ^ regularity) ^ 2) *
          ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
            ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2) := by
  have herror := hdensity.sub (integrable_mollifyDensity hdensity hscale)
  have hcontinuous := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ (integrable_complex_of_real herror)
  have hFourierBound : (∫⁻ frequency : ℝ, ENNReal.ofReal
      (‖𝓕 (fun value => ((density value - mollifyDensity density scale value : ℝ) : ℂ)) frequency‖ ^ 2)) ≤
      ENNReal.ofReal (((2 * Real.pi + 2) * scale ^ regularity) ^ 2) *
        ∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
          ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro frequency
    change ENNReal.ofReal
        (‖𝓕 (fun value => ((density value - mollifyDensity density scale value : ℝ) : ℂ)) frequency‖ ^ 2) ≤
      ENNReal.ofReal (((2 * Real.pi + 2) * scale ^ regularity) ^ 2) *
        ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
          ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2)
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (norm_fourier_mollification_error_sq_le hdensity hscale hregularity hregularityOne frequency)
  have hFourier : MemLp
      (𝓕 (fun value => ((density value - mollifyDensity density scale value : ℝ) : ℂ))) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hcontinuous.aestronglyMeasurable).mpr
    refine ⟨(hcontinuous.norm.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun frequency => sq_nonneg _))]
    exact hFourierBound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top henergy)
  obtain ⟨hLp, hphysical⟩ := classical_signed_density_memLp_and_norm_bound herror hFourier
  refine ⟨hLp, (ENNReal.ofReal_le_ofReal hphysical).trans ?_⟩
  change ENNReal.ofReal (∫ frequency : ℝ,
    ‖𝓕 (fun value => ((density value - mollifyDensity density scale value : ℝ) : ℂ)) frequency‖ ^ 2) ≤ _
  rw [ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hFourier.aestronglyMeasurable).mp hFourier)
    (Eventually.of_forall (fun frequency => sq_nonneg _))]
  exact hFourierBound

end LambdaCantor.AE
