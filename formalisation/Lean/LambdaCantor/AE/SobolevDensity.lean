import LambdaCantor.AE.AlmostEverywhereDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

/-- The Fourier transform of a nonnegative density agrees with that of its
measure, with exactly the Fourier normalization used in the annular estimates. -/
theorem fourier_density_eq_measureFourier {density : ℝ → ℝ}
    (hmeasurable : AEStronglyMeasurable density volume)
    (hnonnegative : ∀ᵐ value : ℝ, 0 ≤ density value) (frequency : ℝ) :
    𝓕 (fun value => (density value : ℂ)) frequency =
      measureFourier (volume.withDensity (fun value => ENNReal.ofReal (density value))) frequency := by
  rw [measureFourier, integral_withDensity_eq_integral_toReal_smul₀
    hmeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun value => ENNReal.ofReal_lt_top))]
  rw [Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [hnonnegative] with value hvalue
  rw [ENNReal.toReal_ofReal hvalue]
  simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul]
  rw [mul_comm value frequency, mul_comm]

/-- Fourier characterization of an actual Sobolev density. The weight is
equivalent to the usual inhomogeneous Sobolev weight for nonnegative regularity. -/
def HasSobolevDensity (probability : Measure ℝ) (regularity : ℝ) : Prop :=
  ∃ density : ℝ → ℝ, Integrable density volume ∧ MemLp density 2 volume ∧
    (∀ᵐ value : ℝ, 0 ≤ density value) ∧
    probability = volume.withDensity (fun value => ENNReal.ofReal (density value)) ∧
    (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
      ‖𝓕 (fun value => (density value : ℂ)) frequency‖ ^ 2)) < ⊤

theorem hasSobolevDensity_of_fullFourierEnergy {ratio regularity : ℝ}
    (henergy : fullFourierEnergy ratio regularity < ⊤) :
    HasSobolevDensity (selfConvolutionProbability ratio) regularity := by
  obtain ⟨density, hintegrable, hLp, hnonnegative, hmeasure⟩ :=
    exists_integrable_convolution_L2_density henergy
  refine ⟨density, hintegrable, hLp, hnonnegative, hmeasure, ?_⟩
  simp_rw [fourier_density_eq_measureFourier hintegrable.aestronglyMeasurable hnonnegative,
    ← hmeasure]
  rwa [← fullFourierEnergy_eq_convolution_energy]

theorem ae_hasSobolevDensity_on_interval
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    ∀ᵐ ratio : ℝ, ratio ∈ Ioo lower upper →
      HasSobolevDensity (selfConvolutionProbability ratio) regularity := by
  filter_upwards [ae_finite_fullFourierEnergy_on_interval hlower horder hupper hregularity hrange]
    with ratio hfinite
  exact fun hinside => hasSobolevDensity_of_fullFourierEnergy (hfinite hinside)

end LambdaCantor.AE
