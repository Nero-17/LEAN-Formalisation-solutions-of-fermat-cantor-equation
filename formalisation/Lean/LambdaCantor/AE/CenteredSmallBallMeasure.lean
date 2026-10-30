import LambdaCantor.AE.PairedAddressStreams
import LambdaCantor.Last.BinaryMeasure

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace LambdaCantor.AE

/-- The fair-bit law in the binary cylinder module agrees with the uniform law. -/
theorem uniform_bit_eq_binary_fairBit : (PMF.uniformOfFintype Bool).toMeasure = Last.fairBit := by
  apply Measure.ext_of_singleton
  intro bit
  simp [Last.fairBit_singleton, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]

theorem paired_first_stream_law :
    First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) =
      Last.binaryBranchMeasure := by
  have mapped := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => (PMF.uniformOfFintype (Bool × Bool)).toMeasure)
    (f := fun _ pair => pair.1) (by fun_prop)
  simpa only [First.Roots.pairedAddressMeasure, fair_paired_digit_product, fairDigitMeasure,
    Measure.map_fst_prod, measure_univ, one_smul, uniform_bit_eq_binary_fairBit,
    Last.binaryBranchMeasure] using mapped

theorem paired_second_stream_law :
    First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) =
      Last.binaryBranchMeasure := by
  have mapped := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => (PMF.uniformOfFintype (Bool × Bool)).toMeasure)
    (f := fun _ pair => pair.2) (by fun_prop)
  simpa only [First.Roots.pairedAddressMeasure, fair_paired_digit_product, fairDigitMeasure,
    Measure.map_snd_prod, measure_univ, one_smul, uniform_bit_eq_binary_fairBit,
    Last.binaryBranchMeasure] using mapped

/-- Exact coordinate disintegration of the actual paired address measure. -/
theorem paired_streams_product_law :
    First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
      ((fun index => (digits index).1), (fun index => (digits index).2))) =
      Last.binaryBranchMeasure.prod Last.binaryBranchMeasure := by
  rw [paired_address_streams_independent.map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun index => (measurable_pi_apply index).fst)).aemeasurable
    (measurable_pi_lambda _ (fun index => (measurable_pi_apply index).snd)).aemeasurable,
    paired_first_stream_law, paired_second_stream_law]

theorem rootLaw_eq_binary_product (root : (ℕ → Bool × Bool) → ℝ)
    (root_measurable : Measurable root) :
    First.Roots.rootLaw root = (Last.binaryBranchMeasure.prod Last.binaryBranchMeasure).map
      (fun streams : (ℕ → Bool) × (ℕ → Bool) => root (fun index => (streams.1 index, streams.2 index))) := by
  rw [← paired_streams_product_law, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A short root interval containing at most one first-coordinate cylinder in
each second-coordinate slice has mass at most the fair binary cylinder mass. -/
theorem rootLaw_small_interval_of_prefix_separation
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    (depth : ℕ) {left right : ℝ}
    (prefix_unique : ∀ second first other : ℕ → Bool,
      root (fun index => (first index, second index)) ∈ Set.Icc left right →
      root (fun index => (other index, second index)) ∈ Set.Icc left right →
      ∀ index < depth, first index = other index) :
    First.Roots.rootLaw root (Set.Icc left right) ≤ (2 : ℝ≥0∞)⁻¹^depth := by
  classical
  rw [rootLaw_eq_binary_product root root_measurable,
    Measure.map_apply (by fun_prop) measurableSet_Icc,
    Measure.prod_apply_symm (measurableSet_Icc.preimage (by fun_prop))]
  calc
    _ ≤ ∫⁻ _second, (2 : ℝ≥0∞)⁻¹^depth ∂Last.binaryBranchMeasure := by
      apply lintegral_mono
      intro second
      by_cases inhabited : ∃ first : ℕ → Bool,
          root (fun index => (first index, second index)) ∈ Set.Icc left right
      · obtain ⟨first, first_mem⟩ := inhabited
        apply le_trans (measure_mono (show
          {other : ℕ → Bool | root (fun index => (other index, second index)) ∈ Set.Icc left right} ⊆
            Last.branchCylinder depth first from ?_))
          (Last.binaryBranchMeasure_cylinder depth first).le
        intro other other_mem index before
        exact prefix_unique second other first other_mem first_mem index before
      · have empty : {first : ℕ → Bool |
          root (fun index => (first index, second index)) ∈ Set.Icc left right} = ∅ := by
          ext first
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
          exact iff_false_intro (fun inside => inhabited ⟨first, inside⟩)
        change Last.binaryBranchMeasure {first : ℕ → Bool |
          root (fun index => (first index, second index)) ∈ Set.Icc left right} ≤ (2 : ℝ≥0∞)⁻¹ ^ depth
        rw [empty, measure_empty]
        exact zero_le
    _ = _ := by simp

end LambdaCantor.AE
