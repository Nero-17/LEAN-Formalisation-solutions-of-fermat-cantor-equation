import LambdaCantor.AE.SobolevTransportDensitySupport
import LambdaCantor.AE.SobolevTransportOptimization

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

/-- The sharp smoothing/coupling interpolation, for actual probability
densities and their actual Fourier Sobolev energies. The coupling can be the
common address law used in the freezing argument. -/
theorem exists_density_transport_constant {radius : ℝ} (hradius : 0 ≤ radius) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (first second : ℝ → ℝ) (regularity bound : ℝ),
      Integrable first → Integrable second →
      (∀ᵐ value : ℝ, 0 ≤ first value) → (∀ᵐ value : ℝ, 0 ≤ second value) →
      Function.support first ⊆ Icc (-radius) radius →
      Function.support second ⊆ Icc (-radius) radius →
      0 < regularity → regularity ≤ 1 → 1 ≤ bound →
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
        ‖𝓕 (fun value => (first value : ℂ)) frequency‖ ^ 2)) ≤ ENNReal.ofReal (bound ^ 2) →
      (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + |frequency| ^ (2 * regularity)) *
        ‖𝓕 (fun value => (second value : ℂ)) frequency‖ ^ 2)) ≤ ENNReal.ofReal (bound ^ 2) →
      ∀ (coupling : Measure (ℝ × ℝ)), IsProbabilityMeasure coupling →
      Integrable (fun sample : ℝ × ℝ => |sample.1 - sample.2|) coupling →
      coupling.map Prod.fst = volume.withDensity (fun value => ENNReal.ofReal (first value)) →
      coupling.map Prod.snd = volume.withDensity (fun value => ENNReal.ofReal (second value)) →
      (∫ value : ℝ, |first value - second value|) ≤
        constant * bound ^ (1 / (1 + regularity)) *
          (∫ sample : ℝ × ℝ, |sample.1 - sample.2| ∂coupling) ^
            (regularity / (1 + regularity)) := by
  obtain ⟨translationConstant, htranslationConstant, htranslation⟩ :=
    exists_transportMollifier_translation_bound
  refine ⟨2 * Real.sqrt (2 * (radius + 1)) * (2 * Real.pi + 2) +
      translationConstant + 2, by positivity, ?_⟩
  intro first second regularity bound hfirst hsecond hfirstNonnegative hsecondNonnegative
    hfirstSupport hsecondSupport hregularity hregularityOne hbound hfirstEnergy hsecondEnergy
    coupling hprobability hcost hfirstLaw hsecondLaw
  letI : IsProbabilityMeasure coupling := hprobability
  letI : IsProbabilityMeasure (coupling.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (coupling.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hfirstMass := integral_probability_density_eq_one (coupling.map Prod.fst)
    hfirst hfirstNonnegative hfirstLaw
  have hsecondMass := integral_probability_density_eq_one (coupling.map Prod.snd)
    hsecond hsecondNonnegative hsecondLaw
  have htwo := probability_density_L1_distance_le_two hfirst hsecond
    hfirstNonnegative hsecondNonnegative hfirstMass hsecondMass
  apply sobolev_transport_optimization
    (cost := ∫ sample : ℝ × ℝ, |sample.1 - sample.2| ∂coupling)
    (firstConstant := 2 * Real.sqrt (2 * (radius + 1)) * (2 * Real.pi + 2)) hbound
    (integral_nonneg (fun sample : ℝ × ℝ => abs_nonneg (sample.1 - sample.2)))
    hregularity (by positivity) htranslationConstant.le htwo
  intro scale hscale hscaleOne
  have hsmoothing := density_L1_smoothing_coupling_bound hfirst hsecond
    hfirstNonnegative hsecondNonnegative hradius hscale hscaleOne hregularity.le
    hregularityOne (by linarith) hfirstSupport hsecondSupport hfirstEnergy hsecondEnergy
    htranslation coupling hcost hfirstLaw hsecondLaw
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hsmoothing

end LambdaCantor.AE
