import LambdaCantor.First.RootsPrefixTailLaw
import LambdaCantor.First.RootsKernelNeighborhoods

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

open scoped Classical in
/-- The actual neighborhood-truncated kernel law is exactly a finite sum of
unrestricted fresh-tail laws, each with its original Bernoulli cylinder mass. -/
theorem selectedRootKernel_law_eq_sum {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) :
    (pairedAddressMeasure.restrict (prefixNeighborhood selected depth)).map
      (selectedRootKernel data selected depth) =
      ∑ word : Fin depth → Bool × Bool,
        if ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index then
          ((4 : ℝ≥0∞)⁻¹ ^ depth) • completeRootKernelLaw data (prefixRepresentative selected depth word) depth
        else 0 := by
  classical
  let admissible : Set (Fin depth → Bool × Bool) :=
    {word | ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index}
  let split : (ℕ → Bool × Bool) → (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) :=
    fun digits => ((fun index => digits index), fun index => digits (index + depth))
  let combine : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) → ℝ :=
    fun pair => completeRootKernel data (prefixRepresentative selected depth pair.1) depth pair.2
  have admissible_measurable : MeasurableSet admissible := (Set.toFinite _).measurableSet
  have split_measurable : Measurable split := by fun_prop
  have combine_measurable : Measurable combine :=
    (continuous_prod_of_discrete_left.mpr (fun word =>
      continuous_completeRootKernel data (prefixRepresentative selected depth word) depth)).measurable
  have preimage : split ⁻¹' (admissible ×ˢ Set.univ) = prefixNeighborhood selected depth := by
    ext digits
    simp only [split, admissible, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true,
      Set.mem_setOf_eq, prefixNeighborhood]
    constructor
    · rintro ⟨representative, member, agreement⟩
      exact ⟨representative, member, fun index before => agreement ⟨index, before⟩⟩
    · rintro ⟨representative, member, agreement⟩
      exact ⟨representative, member, fun index => agreement index index.isLt⟩
  have split_law : (pairedAddressMeasure.restrict (prefixNeighborhood selected depth)).map split =
      ((pairedWordMeasure depth).restrict admissible).prod pairedAddressMeasure := by
    rw [Measure.restrict_prod_eq_prod_univ, ← paired_prefix_tail_law depth,
      Measure.restrict_map split_measurable (admissible_measurable.prod MeasurableSet.univ), preimage]
  have mapped : (pairedAddressMeasure.restrict (prefixNeighborhood selected depth)).map
      (selectedRootKernel data selected depth) =
      (((pairedWordMeasure depth).restrict admissible).prod pairedAddressMeasure).map combine := by
    rw [← split_law, Measure.map_map combine_measurable split_measurable]
    rfl
  rw [mapped, pairedWordMeasure_eq_sum, Measure.restrict_sum _ admissible_measurable,
    Measure.prod_sum_left, Measure.map_sum combine_measurable.aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro word _
  rw [Measure.restrict_smul, MeasureTheory.restrict_dirac]
  by_cases member : word ∈ admissible
  · have witness : ∃ representative ∈ selected,
        ∀ index : Fin depth, representative index = word index := member
    simp only [member, witness, if_pos, Measure.prod_smul_left, Measure.dirac_prod, Measure.map_smul,
      Measure.map_map combine_measurable measurable_prodMk_left]
    rfl
  · simp [member, show ¬∃ representative ∈ selected,
        ∀ index : Fin depth, representative index = word index from member]

end LambdaCantor.First.Roots
