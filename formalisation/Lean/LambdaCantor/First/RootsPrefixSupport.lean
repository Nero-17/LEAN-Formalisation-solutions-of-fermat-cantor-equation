import LambdaCantor.First.RootsConditionalDensities
import LambdaCantor.First.RootsPrefixThreshold

noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace LambdaCantor.First.Roots

/-- Positive canonical prefix density comes from an actual address in the
selected compact prefix. The exceptional set is Lebesgue null. -/
theorem goodSetPrefixDensity_actual_range {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool) :
    ∀ᵐ parameter ∂volume, 0 < goodSetPrefixDensity data orderIndex bound depth word parameter →
      ∃ digits ∈ rootSobolevGoodSet data orderIndex bound,
        digits ∈ finitePairedPrefix word ∧ data.root digits = parameter := by
  have properties := goodSetRootDensity_properties data orderIndex bound
  have supported := goodSetRootConditional_ae_selected_fibre data orderIndex bound
  rw [properties.2.2.2] at supported
  have lebesgue_supported := (ae_withDensity_iff properties.2.1.ennreal_ofReal).mp supported
  filter_upwards [lebesgue_supported] with parameter conditional_support positive
  have density_ne_zero : goodSetRootDensity data orderIndex bound parameter ≠ 0 := by
    intro zero
    simp only [goodSetPrefixDensity, zero, zero_mul, mul_zero, lt_self_iff_false] at positive
  have density_positive : 0 < goodSetRootDensity data orderIndex bound parameter := by
    have nonnegative := properties.1 parameter
    exact lt_of_le_of_ne nonnegative (Ne.symm density_ne_zero)
  have conditional_prefix_ne_zero :
      goodSetRootConditional data orderIndex bound parameter (finitePairedPrefix word) ≠ 0 := by
    intro zero
    simp only [goodSetPrefixDensity, zero, ENNReal.toReal_zero, mul_zero, lt_self_iff_false] at positive
  have selected_fibre := conditional_support (ENNReal.ofReal_ne_zero_iff.mpr density_positive)
  by_contra no_address
  have outside_prefix : ∀ᵐ digits ∂goodSetRootConditional data orderIndex bound parameter,
      digits ∉ finitePairedPrefix word := by
    filter_upwards [selected_fibre] with digits selected
    intro prefix_member
    exact no_address ⟨digits, selected.1, prefix_member, selected.2⟩
  have zero_prefix : goodSetRootConditional data orderIndex bound parameter (finitePairedPrefix word) = 0 := by
    simpa only [not_not, Set.setOf_mem_eq] using ae_iff.mp outside_prefix
  exact conditional_prefix_ne_zero zero_prefix

/-- The coherent actual prefix density is supported near its actual chosen
representative root at the genuine geometric scale. -/
theorem goodSetPrefixDensity_near_representative {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ orderIndex bound depth : ℕ, minimumDepth ≤ depth →
      ∀ word : Fin depth → Bool × Bool, ∀ᵐ parameter ∂volume,
        0 < goodSetPrefixDensity data orderIndex bound depth word parameter →
          |parameter - data.root (prefixRepresentative (rootSobolevGoodSet data orderIndex bound) depth word)| ≤
            (4 * exponent / data.derivative_lower_bound) *
              data.root (prefixRepresentative (rootSobolevGoodSet data orderIndex bound) depth word) ^ depth := by
  obtain ⟨minimumDepth, roots_close⟩ := rootFibreData_root_displacement data
  refine ⟨minimumDepth, ?_⟩
  intro orderIndex bound depth depth_ge word
  filter_upwards [goodSetPrefixDensity_actual_range data orderIndex bound depth word]
    with parameter parameter_property positive
  obtain ⟨digits, _, prefix_member, root_eq⟩ := parameter_property positive
  have agreement : ∀ index < depth, digits index =
      prefixRepresentative (rootSobolevGoodSet data orderIndex bound) depth word index := by
    intro index before
    exact (prefix_member ⟨index, before⟩).trans
      (prefixRepresentative_matches _ depth word ⟨index, before⟩).symm
  simpa only [root_eq, abs_sub_comm] using roots_close digits
    (prefixRepresentative (rootSobolevGoodSet data orderIndex bound) depth word) depth depth_ge agreement

/-- On the actual positive-density support, the variable parameter threshold
is bounded below by half the threshold at the chosen prefix representative. -/
theorem goodSetPrefixDensity_threshold_support {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ orderIndex bound depth : ℕ, minimumDepth ≤ depth →
      ∀ (word : Fin depth → Bool × Bool) (loss : ℝ), ∀ᵐ parameter ∂volume,
        0 < goodSetPrefixDensity data orderIndex bound depth word parameter →
          (1 / 2 : ℝ) *
            data.root (prefixRepresentative (rootSobolevGoodSet data orderIndex bound) depth word) ^ (-(depth : ℝ)) *
              Real.exp (loss * depth) ≤ parameter ^ (-(depth : ℝ)) * Real.exp (loss * depth) := by
  obtain ⟨minimumDepth, threshold⟩ := rootFibreData_density_thresholds data
  refine ⟨minimumDepth, ?_⟩
  intro orderIndex bound depth depth_ge word loss
  filter_upwards [goodSetPrefixDensity_actual_range data orderIndex bound depth word]
    with parameter parameter_property positive
  obtain ⟨digits, _, prefix_member, root_eq⟩ := parameter_property positive
  have agreement : ∀ index < depth,
      prefixRepresentative (rootSobolevGoodSet data orderIndex bound) depth word index = digits index := by
    intro index before
    exact (prefixRepresentative_matches _ depth word ⟨index, before⟩).trans
      (prefix_member ⟨index, before⟩).symm
  simpa only [root_eq] using threshold
    (prefixRepresentative (rootSobolevGoodSet data orderIndex bound) depth word) digits depth depth_ge agreement loss

end LambdaCantor.First.Roots
