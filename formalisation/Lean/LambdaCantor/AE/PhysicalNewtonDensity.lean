import LambdaCantor.AE.NormalizedNewtonDensity
import LambdaCantor.AE.AffineDensityLaw
import LambdaCantor.AE.PositiveDensityRepresentative

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

theorem normalizedNewtonLaw_recover (kernel : FrozenNewtonKernel) (origin : ℝ)
    {width : ℝ} (width_positive : 0 < width) :
    (normalizedNewtonLaw kernel origin width).map (fun value => origin+width*value) = kernel.law := by
  have normalization_measurable : Measurable (fun value : ℝ => (value - origin) / width) := by fun_prop
  have affine_measurable : Measurable (fun value : ℝ => origin + width * value) := by fun_prop
  rw [normalizedNewtonLaw, Measure.map_map affine_measurable normalization_measurable]
  change kernel.law.map (fun value : ℝ => origin + width * ((value - origin) / width)) = kernel.law
  have identity : (fun value : ℝ => origin+width*((value-origin)/width)) = id := by
    funext value
    simp only [id_eq]
    field_simp [width_positive.ne']
    <;> ring
  rw [identity, Measure.map_id]

theorem physicalNewtonLaw_density (kernel : FrozenNewtonKernel) (origin : ℝ)
    {width : ℝ} (width_positive : 0 < width) (density : ℝ → ℝ)
    (integrable : Integrable density) (nonnegative : ∀ value, 0 ≤ density value)
    (normalized_law : normalizedNewtonLaw kernel origin width =
      volume.withDensity (fun value => ENNReal.ofReal (density value))) :
    kernel.law = volume.withDensity
      (fun value => ENNReal.ofReal (physicalAffineDensity origin width density value)) := by
  rw [← normalizedNewtonLaw_recover kernel origin width_positive, normalized_law,
    map_affine_withDensity density integrable nonnegative origin width_positive]

/-- Choose a pointwise nonnegative representative so affine reconstruction
has its actual density identity, while retaining compact support and every
Fourier energy bound of the original finite-energy density. -/
theorem actual_normalized_newton_density (kernel : FrozenNewtonKernel)
    {origin width radius minimumScale regularity : ℝ}
    (width_positive : 0 < width) (minimum_positive : 0 < minimumScale)
    (first_lower : minimumScale ≤ kernel.firstScale/width)
    (second_lower : minimumScale ≤ kernel.secondScale/width)
    (regularity_nonnegative : 0 ≤ regularity)
    (energy_finite : fullFourierEnergy kernel.freezing regularity < ⊤)
    (support_bound : ∀ digits : ℕ → Bool × Bool, |(kernel.value digits-origin)/width| ≤ radius) :
    ∃ density : ℝ → ℝ, Integrable density ∧ MemLp density 2 volume ∧
      (∀ value, 0 ≤ density value) ∧ Function.support density ⊆ Icc (-radius) radius ∧
      normalizedNewtonLaw kernel origin width = volume.withDensity (fun value => ENNReal.ofReal (density value)) ∧
      kernel.law = volume.withDensity (fun value => ENNReal.ofReal (physicalAffineDensity origin width density value)) ∧
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
        ‖𝓕 (fun value => (density value : ℂ)) frequency‖^2)) ≤
        2*(ENNReal.ofReal (1+(minimumScale^(2*regularity))⁻¹)*
          ENNReal.ofReal minimumScale⁻¹*fullFourierEnergy kernel.freezing regularity) := by
  obtain ⟨density, integrable, square_integrable, nonnegative, support, law, weighted⟩ :=
    normalizedNewtonLaw_supported_density kernel minimum_positive first_lower second_lower
      regularity_nonnegative energy_finite support_bound
  have positive_integrable := positiveDensityRepresentative_integrable integrable nonnegative
  have same := positiveDensityRepresentative_ae_eq nonnegative
  have positive_law : normalizedNewtonLaw kernel origin width =
      volume.withDensity (fun value => ENNReal.ofReal (positiveDensityRepresentative density value)) :=
    law.trans (withDensity_congr_ae (same.symm.fun_comp ENNReal.ofReal))
  refine ⟨positiveDensityRepresentative density, positive_integrable,
    positiveDensityRepresentative_memLp square_integrable nonnegative,
    positiveDensityRepresentative_nonnegative density,
    (positiveDensityRepresentative_support density).trans support, positive_law,
    physicalNewtonLaw_density kernel origin width_positive _ positive_integrable
      (positiveDensityRepresentative_nonnegative density) positive_law, ?_⟩
  have same_fourier : 𝓕 (fun value => (positiveDensityRepresentative density value : ℂ)) =
      𝓕 (fun value => (density value : ℂ)) := by
    funext frequency
    rw [Real.fourier_real_eq, Real.fourier_real_eq]
    apply integral_congr_ae
    filter_upwards [same] with value equality
    rw [equality]
  simpa only [same_fourier] using weighted

end LambdaCantor.AE
