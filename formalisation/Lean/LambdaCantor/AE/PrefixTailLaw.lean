import LambdaCantor.First.RootsMeasures
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LambdaCantor.AE

def pairedPrefixMeasure (depth : ℕ) : Measure (Fin depth → Bool × Bool) :=
  First.Roots.pairedAddressMeasure.map (fun digits index => digits index)

theorem paired_prefix_tail_independent (depth : ℕ) :
    IndepFun (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index)
      (fun digits : ℕ → Bool × Bool => fun index : ℕ => digits (index + depth))
      First.Roots.pairedAddressMeasure := by
  have independent : iIndepFun (fun index (digits : ℕ → Bool × Bool) => digits index)
      First.Roots.pairedAddressMeasure :=
    iIndepFun_infinitePi (X := fun _ digit => digit) (by fun_prop)
  have spaces : iIndep (fun index : ℕ => MeasurableSpace.comap
      (fun digits : ℕ → Bool × Bool => digits index) inferInstance)
      First.Roots.pairedAddressMeasure := independent
  have split := indep_iSup_of_disjoint
    (fun index : ℕ => (measurable_pi_apply index).comap_le) spaces
    (S := {index | index < depth}) (T := {index | depth ≤ index})
    (by rw [Set.disjoint_left]; intro index before after
        exact (not_le_of_gt (show index < depth from before)) (show depth ≤ index from after))
  change Indep (MeasurableSpace.comap
    (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) inferInstance)
    (MeasurableSpace.comap
    (fun digits : ℕ → Bool × Bool => fun index : ℕ => digits (index + depth)) inferInstance)
    First.Roots.pairedAddressMeasure
  apply indep_of_indep_of_le split
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun index => le_iSup_of_le index
      (le_iSup_of_le index.isLt le_rfl)
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun index => le_iSup_of_le (index + depth)
      (le_iSup_of_le (show depth ≤ index + depth by omega) le_rfl)

theorem paired_prefix_tail_law (depth : ℕ) :
    First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
      ((fun index : Fin depth => digits index), fun index : ℕ => digits (index + depth))) =
      (pairedPrefixMeasure depth).prod First.Roots.pairedAddressMeasure := by
  have prefix_measurable : Measurable
      (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) :=
    measurable_pi_lambda _ (fun index : Fin depth => measurable_pi_apply (index : ℕ))
  have tail_measurable : Measurable
      (fun digits : ℕ → Bool × Bool => fun index : ℕ => digits (index + depth)) :=
    measurable_pi_lambda _ (fun index => measurable_pi_apply (index + depth))
  rw [(paired_prefix_tail_independent depth).map_prod_eq_prod_map_map
    prefix_measurable.aemeasurable tail_measurable.aemeasurable]
  congr 1
  unfold First.Roots.pairedAddressMeasure
  exact Measure.map_infinitePi_infinitePi_of_inj (fun first second equal => Nat.add_right_cancel equal)

theorem pairedPrefixMeasure_singleton (depth : ℕ) (word : Fin depth → Bool × Bool) :
    pairedPrefixMeasure depth {word} = (4 : ℝ≥0∞)⁻¹ ^ depth := by
  let extension : ℕ → Bool × Bool :=
    fun index => if before : index < depth then word ⟨index, before⟩ else (false, false)
  have identity : (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) ⁻¹' {word} =
      First.Roots.pairedPrefix extension depth := by
    ext digits
    simp only [Set.mem_preimage, Set.mem_singleton_iff, First.Roots.pairedPrefix, Set.mem_setOf_eq]
    constructor
    · intro equality index before
      simpa only [extension, dif_pos before] using congrFun equality ⟨index, before⟩
    · intro agreement
      funext index
      simpa only [extension, dif_pos index.isLt] using agreement index index.isLt
  rw [pairedPrefixMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    identity, First.Roots.pairedPrefix_mass]
  simp only [one_div]

theorem pairedPrefixMeasure_eq_sum (depth : ℕ) :
    pairedPrefixMeasure depth = Measure.sum (fun word : Fin depth → Bool × Bool =>
      ((4 : ℝ≥0∞)⁻¹ ^ depth) • Measure.dirac word) := by
  rw [← Measure.sum_smul_dirac (pairedPrefixMeasure depth)]
  congr 1
  funext word
  rw [pairedPrefixMeasure_singleton depth word]

/-- Exact law of a full depth mixture, with unrestricted fresh tails and
the original Bernoulli weights. No conditional root law is involved. -/
theorem paired_prefix_observable_law (depth : ℕ)
    (combine : (Fin depth → Bool × Bool) × (ℕ → Bool × Bool) → ℝ)
    (combine_measurable : Measurable combine) :
    First.Roots.pairedAddressMeasure.map
      (fun digits => combine ((fun index : Fin depth => digits index), fun index => digits (index + depth))) =
      ∑ word : Fin depth → Bool × Bool,
        ((4 : ℝ≥0∞)⁻¹ ^ depth) •
          First.Roots.pairedAddressMeasure.map (fun tail => combine (word, tail)) := by
  have split_measurable : Measurable
      (fun digits : ℕ → Bool × Bool =>
        ((fun index : Fin depth => digits index), fun index : ℕ => digits (index + depth))) := by fun_prop
  have mapped : First.Roots.pairedAddressMeasure.map
      (fun digits => combine ((fun index : Fin depth => digits index), fun index => digits (index + depth))) =
      ((pairedPrefixMeasure depth).prod First.Roots.pairedAddressMeasure).map combine := by
    rw [← paired_prefix_tail_law depth, Measure.map_map combine_measurable split_measurable]
    rfl
  rw [mapped, pairedPrefixMeasure_eq_sum, Measure.prod_sum_left,
    Measure.map_sum combine_measurable.aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro word _
  rw [Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map combine_measurable measurable_prodMk_left]
  rfl

end LambdaCantor.AE
