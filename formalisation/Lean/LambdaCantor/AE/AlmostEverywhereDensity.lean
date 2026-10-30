import LambdaCantor.AE.ConvolutionFourierL2
import LambdaCantor.AE.ClassicalDensityCore
import LambdaCantor.AE.ParameterCutoffCover

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

theorem exists_integrable_measure_L2_density (probability : Measure ℝ) [IsFiniteMeasure probability]
    (hLp : MemLp (measureFourier probability) 2 volume) :
    ∃ density : ℝ → ℝ, Integrable density volume ∧ MemLp density 2 volume ∧
      (∀ᵐ value : ℝ, 0 ≤ density value) ∧
      probability = volume.withDensity (fun value => ENNReal.ofReal (density value)) := by
  obtain ⟨density, integrable, square_integrable, nonnegative, law, _⟩ :=
    ExternalPlancherel.finite_measure_L2_density probability hLp
  exact ⟨density, integrable, square_integrable, nonnegative, law⟩

theorem exists_integrable_convolution_L2_density {ratio regularity : ℝ}
    (henergy : fullFourierEnergy ratio regularity < ⊤) :
    ∃ density : ℝ → ℝ, Integrable density volume ∧ MemLp density 2 volume ∧
      (∀ᵐ value : ℝ, 0 ≤ density value) ∧
      selfConvolutionProbability ratio = volume.withDensity (fun value => ENNReal.ofReal (density value)) :=
  exists_integrable_measure_L2_density _ (convolutionFourier_memLp_two_of_fullEnergy henergy)

/-- The actual self-convolution has an L¹ ∩ L² density for almost every
parameter in every interval satisfying the paper's strict Sobolev range. -/
theorem ae_exists_convolution_L2_density_on_interval
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    ∀ᵐ ratio : ℝ, ratio ∈ Ioo lower upper →
      ∃ density : ℝ → ℝ, Integrable density volume ∧ MemLp density 2 volume ∧
        (∀ᵐ value : ℝ, 0 ≤ density value) ∧
        selfConvolutionProbability ratio =
          volume.withDensity (fun value => ENNReal.ofReal (density value)) := by
  filter_upwards [ae_finite_fullFourierEnergy_on_interval hlower horder hupper hregularity hrange]
    with ratio hfinite
  exact fun hinside => exists_integrable_convolution_L2_density (hfinite hinside)

end LambdaCantor.AE
