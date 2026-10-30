import LambdaCantor.AE.ConvolutionMeasure
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory Filter

namespace LambdaCantor.AE

theorem measurable_convolutionFourier (ratio : ℝ) :
    Measurable (measureFourier (selfConvolutionProbability ratio)) := by
  simp_rw [show measureFourier (selfConvolutionProbability ratio) =
      fun frequency => addressFourier ratio frequency ^ 2 from
    funext (measureFourier_selfConvolutionProbability ratio)]
  exact (measurable_addressFourier ratio).pow_const 2

/-- Actual L2 Fourier transform of the actual convolution measure, derived from the proved-source
full energy. This is a Fourier-space statement; an L2 density is a further conclusion. -/
theorem convolutionFourier_memLp_two_of_fullEnergy {ratio regularity : ℝ}
    (henergy : fullFourierEnergy ratio regularity < ⊤) :
    MemLp (measureFourier (selfConvolutionProbability ratio)) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_convolutionFourier ratio).aestronglyMeasurable).mpr
  refine ⟨((measurable_convolutionFourier ratio).norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun _ => sq_nonneg _))]
  apply lt_of_le_of_lt _ henergy
  unfold fullFourierEnergy
  apply lintegral_mono
  intro frequency
  change ENNReal.ofReal (‖measureFourier (selfConvolutionProbability ratio) frequency‖ ^ 2) ≤
    ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) * ‖addressFourier ratio frequency‖ ^ 4)
  rw [norm_measureFourier_selfConvolution_sq]
  apply ENNReal.ofReal_le_ofReal
  have hweight := Real.rpow_nonneg (abs_nonneg frequency) (2 * regularity)
  have hnorm := pow_nonneg (norm_nonneg (addressFourier ratio frequency)) 4
  nlinarith

theorem ae_convolutionFourier_memLp_two_on_positive_cutoff
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Set.Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    ∀ᵐ ratio : ℝ, 0 < parameterCutoff ratio →
      MemLp (measureFourier (selfConvolutionProbability ratio)) 2 volume := by
  filter_upwards [ae_finite_fullFourierEnergy hlower horder hupper hregularity hrange
    parameterCutoff hsmooth hcompact hsupport hnonnegative] with ratio hfinite
  exact fun hpositive => convolutionFourier_memLp_two_of_fullEnergy (hfinite hpositive)

end LambdaCantor.AE
