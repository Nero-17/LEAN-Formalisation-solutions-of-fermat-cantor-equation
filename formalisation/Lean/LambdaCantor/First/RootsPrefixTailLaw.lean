import LambdaCantor.First.RootsKernelLaws
import LambdaCantor.First.RootsKernelSelection

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

def pairedWordMeasure (depth : ℕ) : Measure (Fin depth → Bool × Bool) :=
  pairedAddressMeasure.map (fun digits index => digits index)

theorem paired_prefix_tail_independent (depth : ℕ) :
    IndepFun (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index)
      (fun digits : ℕ → Bool × Bool => fun index : ℕ => digits (index + depth)) pairedAddressMeasure := by
  have independent : iIndepFun (fun index (digits : ℕ → Bool × Bool) => digits index)
      pairedAddressMeasure := iIndepFun_infinitePi (X := fun _ digit => digit) (by fun_prop)
  have spaces : iIndep (fun index : ℕ => MeasurableSpace.comap
      (fun digits : ℕ → Bool × Bool => digits index) inferInstance) pairedAddressMeasure := independent
  have split := indep_iSup_of_disjoint
    (fun index : ℕ => (measurable_pi_apply index).comap_le) spaces
    (S := {index | index < depth}) (T := {index | depth ≤ index})
    (by
      rw [Set.disjoint_left]
      intro index before after
      change index < depth at before
      change depth ≤ index at after
      omega)
  change Indep (MeasurableSpace.comap
    (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) inferInstance)
    (MeasurableSpace.comap
    (fun digits : ℕ → Bool × Bool => fun index : ℕ => digits (index + depth)) inferInstance)
    pairedAddressMeasure
  apply indep_of_indep_of_le split
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun index => le_iSup_of_le index
      (le_iSup_of_le index.isLt le_rfl)
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun index => le_iSup_of_le (index + depth)
      (le_iSup_of_le (show depth ≤ index + depth by omega) le_rfl)

theorem paired_prefix_tail_law (depth : ℕ) :
    pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
      ((fun index : Fin depth => digits index), fun index : ℕ => digits (index + depth))) =
      (pairedWordMeasure depth).prod pairedAddressMeasure := by
  have prefix_measurable : Measurable (fun digits : ℕ → Bool × Bool =>
      fun index : Fin depth => digits index) :=
    (continuous_pi (fun index : Fin depth =>
      (continuous_apply (index : ℕ) : Continuous (fun digits : ℕ → Bool × Bool => digits index)))).measurable
  have tail_measurable : Measurable (fun digits : ℕ → Bool × Bool =>
      fun index : ℕ => digits (index + depth)) :=
    (continuous_pi (fun index : ℕ =>
      (continuous_apply (index + depth) : Continuous (fun digits : ℕ → Bool × Bool => digits (index + depth))))).measurable
  rw [(paired_prefix_tail_independent depth).map_prod_eq_prod_map_map
    prefix_measurable.aemeasurable tail_measurable.aemeasurable]
  congr 1
  unfold pairedAddressMeasure
  exact Measure.map_infinitePi_infinitePi_of_inj (fun first second equal => Nat.add_right_cancel equal)

theorem pairedWordMeasure_singleton (depth : ℕ) (word : Fin depth → Bool × Bool) :
    pairedWordMeasure depth {word} = (4 : ℝ≥0∞)⁻¹ ^ depth := by
  let extension := prefixRepresentative Set.univ depth word
  have identity : (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) ⁻¹' {word} =
      pairedPrefix extension depth := by
    ext digits
    simp only [Set.mem_preimage, Set.mem_singleton_iff, pairedPrefix, Set.mem_setOf_eq]
    constructor
    · intro equality index before
      exact (congrFun equality ⟨index, before⟩).trans
        (prefixRepresentative_matches Set.univ depth word ⟨index, before⟩).symm
    · intro agreement
      funext index
      exact (agreement index index.isLt).trans (prefixRepresentative_matches Set.univ depth word index)
  rw [pairedWordMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton _), identity,
    pairedPrefix_mass]
  simp only [one_div]

theorem pairedWordMeasure_eq_sum (depth : ℕ) :
    pairedWordMeasure depth = Measure.sum (fun word : Fin depth → Bool × Bool =>
      ((4 : ℝ≥0∞)⁻¹ ^ depth) • Measure.dirac word) := by
  rw [← Measure.sum_smul_dirac (pairedWordMeasure depth)]
  congr 1
  funext word
  rw [pairedWordMeasure_singleton]

end LambdaCantor.First.Roots
