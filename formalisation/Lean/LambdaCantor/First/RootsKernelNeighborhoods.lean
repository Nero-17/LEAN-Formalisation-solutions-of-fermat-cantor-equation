import LambdaCantor.First.RootsKernelSelection
import Mathlib.Topology.MetricSpace.PiNat

noncomputable section
open Filter Topology MeasureTheory
namespace LambdaCantor.First.Roots

def prefixNeighborhood (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) : Set (ℕ → Bool × Bool) :=
  {digits | ∃ representative ∈ selected, ∀ index < depth, representative index = digits index}

theorem measurableSet_prefixNeighborhood (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) :
    MeasurableSet (prefixNeighborhood selected depth) := by
  have restriction_continuous : Continuous (fun digits : ℕ → Bool × Bool =>
      fun index : Fin depth => digits index) :=
    continuous_pi (fun index =>
      (continuous_apply (index : ℕ) :
        Continuous (fun digits : ℕ → Bool × Bool => digits (index : ℕ))))
  have identity : prefixNeighborhood selected depth =
      (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) ⁻¹'
      {word | ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index} := by
    ext digits
    constructor
    · rintro ⟨representative, member, agreement⟩
      exact ⟨representative, member, fun index => agreement index index.isLt⟩
    · rintro ⟨representative, member, agreement⟩
      exact ⟨representative, member, fun index before => agreement ⟨index, before⟩⟩
  rw [identity]
  exact ((Set.toFinite _).measurableSet).preimage restriction_continuous.measurable

/-- Closed source sets are recovered pointwise by their finite cylinder neighborhoods. -/
theorem prefixNeighborhood_eventually (selected : Set (ℕ → Bool × Bool))
    (closed : IsClosed selected) (digits : ℕ → Bool × Bool) :
    ∀ᶠ depth in atTop, (digits ∈ prefixNeighborhood selected depth ↔ digits ∈ selected) := by
  by_cases member : digits ∈ selected
  · exact Filter.Eventually.of_forall (fun depth =>
      ⟨fun _ => member, fun _ => ⟨digits, member, fun _ _ => rfl⟩⟩)
  · obtain ⟨neighborhood, ⟨center, depth, rfl⟩, contains, inside⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool × Bool)).exists_subset_of_mem_open
        (show digits ∈ selectedᶜ from member) closed.isOpen_compl
    filter_upwards [eventually_ge_atTop depth] with deeper deeper_ge
    refine ⟨?_, fun impossible => (member impossible).elim⟩
    rintro ⟨representative, representative_mem, agreement⟩
    have representative_cylinder : representative ∈ PiNat.cylinder center depth := by
      apply PiNat.mem_cylinder_iff.mpr
      intro index before
      exact (agreement index (before.trans_le deeper_ge)).trans
        (PiNat.mem_cylinder_iff.mp contains index before)
    exact (inside representative_cylinder representative_mem).elim

/-- This is the weak limit of the actual finite-cylinder truncations used in
kernel replacement, with the actual restricted root law as its limit. -/
theorem prefixNeighborhood_kernel_integral_tendsto {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (closed : IsClosed selected)
    (test : ℝ → ℝ) (test_continuous : Continuous test)
    (bound : ℝ) (test_bounded : ∀ value, ‖test value‖ ≤ bound) :
    Tendsto (fun depth => ∫ digits, (prefixNeighborhood selected depth).indicator
      (fun other => test (selectedRootKernel data selected depth other)) digits ∂pairedAddressMeasure)
      atTop (𝓝 (∫ digits, selected.indicator (fun other => test (data.root other)) digits
        ∂pairedAddressMeasure)) := by
  have bound_nonnegative : 0 ≤ bound := (norm_nonneg (test 0)).trans (test_bounded 0)
  apply tendsto_integral_of_dominated_convergence (fun _ => bound)
  · intro depth
    exact ((test_continuous.comp (continuous_selectedRootKernel data selected depth)).measurable.indicator
      (measurableSet_prefixNeighborhood selected depth)).aestronglyMeasurable
  · exact integrable_const bound
  · intro depth
    apply Filter.Eventually.of_forall
    intro digits
    by_cases member : digits ∈ prefixNeighborhood selected depth
    · simpa only [Set.indicator_of_mem member] using test_bounded (selectedRootKernel data selected depth digits)
    · simpa only [Set.indicator_of_notMem member, norm_zero] using bound_nonnegative
  · apply Filter.Eventually.of_forall
    intro digits
    have eventually_membership := prefixNeighborhood_eventually selected closed digits
    by_cases member : digits ∈ selected
    · rw [Set.indicator_of_mem member]
      apply (test_continuous.continuousAt.tendsto.comp (selectedRootKernel_tendsto data selected digits)).congr'
      filter_upwards [eventually_membership] with depth equivalent
      exact (Set.indicator_of_mem (equivalent.mpr member)
        (fun other => test (selectedRootKernel data selected depth other))).symm
    · rw [Set.indicator_of_notMem member]
      apply (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))).congr'
      filter_upwards [eventually_membership] with depth equivalent
      exact (Set.indicator_of_notMem (fun present => member (equivalent.mp present))
        (fun other => test (selectedRootKernel data selected depth other))).symm

end LambdaCantor.First.Roots
