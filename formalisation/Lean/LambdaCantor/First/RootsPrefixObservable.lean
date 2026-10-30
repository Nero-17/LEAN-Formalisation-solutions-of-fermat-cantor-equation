import LambdaCantor.First.RootsKernelSum

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

open scoped Classical in
/-- Finite-prefix disintegration for any actual measurable observable of a
prefix and its unrestricted fresh tail. This common child-word indexing is
used for both retained parent kernels and replacement child kernels. -/
theorem prefixRestrictedLaw_eq_sum
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ)
    (combine : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) → ℝ)
    (combine_measurable : Measurable combine) :
    (pairedAddressMeasure.restrict (prefixNeighborhood selected depth)).map
      (fun digits => combine ((fun index : Fin depth => digits index), fun index => digits (index + depth))) =
      ∑ word : Fin depth → Bool × Bool,
        if ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index then
          ((4 : ℝ≥0∞)⁻¹ ^ depth) • pairedAddressMeasure.map (fun tail => combine (word, tail))
        else 0 := by
  classical
  let admissible : Set (Fin depth → Bool × Bool) :=
    {word | ∃ representative ∈ selected, ∀ index : Fin depth, representative index = word index}
  let split : (ℕ → Bool × Bool) → (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) :=
    fun digits => ((fun index => digits index), fun index => digits (index + depth))
  have admissible_measurable : MeasurableSet admissible := (Set.toFinite _).measurableSet
  have split_measurable : Measurable split := by fun_prop
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
      (fun digits => combine ((fun index : Fin depth => digits index), fun index => digits (index + depth))) =
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


