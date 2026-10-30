import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

namespace LambdaCantor.Integer

private theorem finite_positive_lower_bound {ι : Type*} (selected : Finset ι)
    (margin : ι → ℝ) (positive : ∀ i ∈ selected, 0 < margin i) :
    ∃ uniform > 0, ∀ i ∈ selected, uniform ≤ margin i := by
  classical
  revert positive
  induction selected using Finset.induction_on with
  | empty => intro _; exact ⟨1, zero_lt_one, by simp⟩
  | @insert i selected absent ih =>
    intro positive
    obtain ⟨uniform, uniformPositive, uniformLower⟩ := ih (by
      intro j hj
      exact positive j (Finset.mem_insert_of_mem hj))
    refine ⟨min (margin i) uniform,
      lt_min (positive i (Finset.mem_insert_self _ _)) uniformPositive, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | member
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (uniformLower j member)

/-- Compactness turns pointwise strict return certificates into finitely many
certificates with one positive margin. The function `gap` can be the minimum
of the finitely many endpoint margins belonging to a pair of return words. -/
theorem compact_uniform_strict_margin {X ι : Type*} [TopologicalSpace X]
    (source : Set X) (compact : IsCompact source) (gap : ι → X → ℝ)
    (continuous : ∀ i, Continuous (gap i))
    (pointwise : ∀ x ∈ source, ∃ i, 0 < gap i x) :
    ∃ selected : Finset ι, ∃ uniform > 0,
      ∀ x ∈ source, ∃ i ∈ selected, uniform < gap i x := by
  classical
  let openSets (i : ι × {ε : ℝ // 0 < ε}) : Set X := {x | i.2.val < gap i.1 x}
  have openCover : ∀ i, IsOpen (openSets i) := by
    intro i
    exact isOpen_lt continuous_const (continuous i.1)
  have covers : source ⊆ ⋃ i, openSets i := by
    intro x hx
    obtain ⟨i, hi⟩ := pointwise x hx
    apply Set.mem_iUnion.mpr
    refine ⟨(i, ⟨gap i x / 2, by linarith⟩), ?_⟩
    change gap i x / 2 < gap i x
    linarith
  obtain ⟨finiteCover, covered⟩ := compact.elim_finite_subcover openSets openCover covers
  obtain ⟨uniform, uniformPositive, uniformLower⟩ := finite_positive_lower_bound
    finiteCover (fun i => i.2.val) (fun i _ => i.2.property)
  refine ⟨finiteCover.image Prod.fst, uniform, uniformPositive, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (covered hx)
  obtain ⟨member, strict⟩ := Set.mem_iUnion.mp hi
  refine ⟨i.1, Finset.mem_image.mpr ⟨i, member, rfl⟩, ?_⟩
  exact lt_of_le_of_lt (uniformLower i member) strict

end LambdaCantor.Integer
