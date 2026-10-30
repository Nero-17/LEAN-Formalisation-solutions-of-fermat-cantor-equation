import LambdaCantor.AE.SobolevTransportMixture
import LambdaCantor.AE.AffineDensityScaling

noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LambdaCantor.AE

/-- One constant works for every finite mixture and every collection of
positive physical widths. Each component pair is normalized in its own
common affine coordinate, and its L1 estimate is transferred back exactly. -/
theorem exists_normalized_finite_mixture_transport_constant
    {Index : Type*} [Fintype Index] {radius : ℝ} (radius_nonnegative : 0 ≤ radius) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (weight amplitude origin width : Index → ℝ) (first second : Index → ℝ → ℝ)
        (regularity cost : ℝ),
      (∀ index, 0 ≤ weight index) → (∑ index, weight index) = 1 →
      (∀ index, 1 ≤ amplitude index) → (∀ index, 0 < width index) →
      (∀ index, Integrable (first index)) → (∀ index, Integrable (second index)) →
      (∀ index, ∀ᵐ value : ℝ, 0 ≤ first index value) →
      (∀ index, ∀ᵐ value : ℝ, 0 ≤ second index value) →
      (∀ index, Function.support (first index) ⊆ Icc (-radius) radius) →
      (∀ index, Function.support (second index) ⊆ Icc (-radius) radius) →
      0 < regularity → regularity ≤ 1 → 0 ≤ cost →
      (∀ index, (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
        ‖𝓕 (fun value => (first index value : ℂ)) frequency‖^2)) ≤ ENNReal.ofReal (amplitude index^2)) →
      (∀ index, (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
        ‖𝓕 (fun value => (second index value : ℂ)) frequency‖^2)) ≤ ENNReal.ofReal (amplitude index^2)) →
      ∀ (coupling : Index → Measure (ℝ × ℝ)),
      (∀ index, IsProbabilityMeasure (coupling index)) →
      (∀ index, Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (coupling index)) →
      (∀ index, (coupling index).map Prod.fst =
        volume.withDensity (fun value => ENNReal.ofReal (first index value))) →
      (∀ index, (coupling index).map Prod.snd =
        volume.withDensity (fun value => ENNReal.ofReal (second index value))) →
      (∀ index, (∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂coupling index) ≤ cost) →
      (∫ value : ℝ, |(∑ index, weight index*physicalAffineDensity (origin index) (width index) (first index) value)-
        ∑ index, weight index*physicalAffineDensity (origin index) (width index) (second index) value|) ≤
          constant*(∑ index, weight index*amplitude index^2)^(1/(2*(1+regularity)))*
            cost^(regularity/(1+regularity)) := by
  obtain ⟨constant, constant_positive, transport⟩ := exists_density_transport_constant radius_nonnegative
  refine ⟨constant, constant_positive, ?_⟩
  intro weight amplitude origin width first second regularity cost weight_nonnegative weight_sum
    amplitude_lower width_positive first_integrable second_integrable first_nonnegative second_nonnegative
    first_support second_support regularity_positive regularity_le_one cost_nonnegative
    first_energy second_energy coupling coupling_probability coupling_integrable first_law second_law coupling_cost
  apply finite_mixture_transport_bound Finset.univ weight amplitude
    (fun index => physicalAffineDensity (origin index) (width index) (first index))
    (fun index => physicalAffineDensity (origin index) (width index) (second index))
    (fun index _ => weight_nonnegative index) weight_sum
    (fun index _ => by linarith [amplitude_lower index])
    (fun index _ => integrable_physicalAffineDensity (first_integrable index) (origin index) (width_positive index))
    (fun index _ => integrable_physicalAffineDensity (second_integrable index) (origin index) (width_positive index))
    constant_positive.le cost_nonnegative regularity_positive.le
  intro index _
  have amplitude_nonnegative : 0 ≤ amplitude index := by linarith [amplitude_lower index]
  rw [physicalAffineDensity_L1_distance (first index) (second index) (origin index) (width_positive index)]
  have component := transport (first index) (second index) regularity (amplitude index)
    (first_integrable index) (second_integrable index) (first_nonnegative index) (second_nonnegative index)
    (first_support index) (second_support index) regularity_positive regularity_le_one (amplitude_lower index)
    (first_energy index) (second_energy index) (coupling index) (coupling_probability index)
    (coupling_integrable index) (first_law index) (second_law index)
  apply component.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (integral_nonneg (fun _ => abs_nonneg _)) (coupling_cost index) (by positivity)

end LambdaCantor.AE
