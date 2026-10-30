import LambdaCantor.AE.NormalizedNewtonKernel
import LambdaCantor.AE.AffineSobolevDensity
import LambdaCantor.AE.SobolevTransportDensitySupport

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

theorem normalizedNewtonLaw_compl_support (kernel : FrozenNewtonKernel)
    (origin width radius : ℝ)
    (support_bound : ∀ digits : ℕ → Bool × Bool, |(kernel.value digits-origin)/width| ≤ radius) :
    normalizedNewtonLaw kernel origin width (Icc (-radius) radius)ᶜ = 0 := by
  have map_composition :
      (First.Roots.pairedAddressMeasure.map kernel.value).map
        (fun value : ℝ => (value - origin) / width) =
      First.Roots.pairedAddressMeasure.map
        (fun digits : ℕ → Bool × Bool => (kernel.value digits - origin) / width) := by
    simpa only [Function.comp_def, id_eq] using
      (Measure.map_map (μ := First.Roots.pairedAddressMeasure)
        ((measurable_id.sub_const origin).div_const width) kernel.value_measurable)
  rw [normalizedNewtonLaw, kernel.law_eq_paired_map, map_composition,
    Measure.map_apply (((kernel.value_measurable).sub_const origin).div_const width) measurableSet_Icc.compl]
  have empty : (fun digits : ℕ → Bool × Bool => (kernel.value digits-origin)/width) ⁻¹'
      (Icc (-radius) radius)ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro digits outside
    exact outside (abs_le.mp (support_bound digits))
  simpa only [Function.comp_apply, empty, measure_empty]

/-- Finite energy at the actual freezing parameter gives an actual compactly
supported normalized Newton density. The complete Newton shift and original
Cantor contraction are both retained in the measure identity. -/
theorem normalizedNewtonLaw_supported_density (kernel : FrozenNewtonKernel)
    {origin width radius minimumScale regularity : ℝ}
    (minimum_positive : 0 < minimumScale)
    (first_lower : minimumScale ≤ kernel.firstScale/width)
    (second_lower : minimumScale ≤ kernel.secondScale/width)
    (regularity_nonnegative : 0 ≤ regularity)
    (energy_finite : fullFourierEnergy kernel.freezing regularity < ⊤)
    (support_bound : ∀ digits : ℕ → Bool × Bool, |(kernel.value digits-origin)/width| ≤ radius) :
    ∃ density : ℝ → ℝ, Integrable density ∧ MemLp density 2 volume ∧
      (∀ᵐ value : ℝ, 0 ≤ density value) ∧ Function.support density ⊆ Icc (-radius) radius ∧
      normalizedNewtonLaw kernel origin width = volume.withDensity (fun value => ENNReal.ofReal (density value)) ∧
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
        ‖𝓕 (fun value => (density value : ℂ)) frequency‖^2)) ≤
        2*(ENNReal.ofReal (1+(minimumScale^(2*regularity))⁻¹)*
          ENNReal.ofReal minimumScale⁻¹*fullFourierEnergy kernel.freezing regularity) := by
  obtain ⟨density, integrable, square_integrable, nonnegative, affine_law, _, weighted⟩ :=
    exists_common_affineSobolev_density (ratio := kernel.freezing)
      (shift := (kernel.affineCenter-origin)/width)
      minimum_positive first_lower second_lower regularity_nonnegative energy_finite
  have law : normalizedNewtonLaw kernel origin width =
      volume.withDensity (fun value => ENNReal.ofReal (density value)) := by
    rw [normalizedNewtonLaw_eq_affine]
    exact affine_law
  obtain ⟨supported, supported_integrable, supported_square, supported_nonnegative, support, supported_law, _, same_fourier⟩ :=
    exists_supported_density_of_measure_support (normalizedNewtonLaw kernel origin width)
      integrable square_integrable nonnegative law (normalizedNewtonLaw_compl_support kernel origin width radius support_bound)
  refine ⟨supported, supported_integrable, supported_square, supported_nonnegative, support, supported_law, ?_⟩
  simpa only [same_fourier] using weighted

end LambdaCantor.AE
