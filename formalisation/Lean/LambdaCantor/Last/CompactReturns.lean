import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith

noncomputable section
namespace LambdaCantor.Last

/-- Compactness turns a pointwise strict-return margin into finitely many choices
with a uniform positive margin, valid on an open neighborhood. The score can be
the minimum of the distances of the two returns from the complement of the level set. -/
theorem compact_uniform_positive_margin {ι : Type*} {levels : Set ℝ}
    (hcompact : IsCompact levels) (hnonempty : levels.Nonempty)
    (score : ι → ℝ → ℝ) (hcontinuous : ∀ index, Continuous (score index))
    (hpositive : ∀ level ∈ levels, ∃ index, 0 < score index level) :
    ∃ (selected : Finset ι) (margin : ℝ) (neighborhood : Set ℝ),
      0 < margin ∧ IsOpen neighborhood ∧ levels ⊆ neighborhood ∧
      ∀ level ∈ neighborhood, ∃ index ∈ selected, margin < score index level := by
  classical
  let domains : (ι × {margin : ℝ // 0 < margin}) → Set ℝ :=
    fun pair => {level | pair.2.val < score pair.1 level}
  have hopen : ∀ pair, IsOpen (domains pair) := by
    intro pair
    exact isOpen_lt continuous_const (hcontinuous pair.1)
  have hcover : levels ⊆ ⋃ pair, domains pair := by
    intro level hlevel
    obtain ⟨index, hindex⟩ := hpositive level hlevel
    apply Set.mem_iUnion.mpr
    refine ⟨(index, ⟨score index level / 2, by linarith⟩), ?_⟩
    change score index level / 2 < score index level
    linarith
  obtain ⟨finite, hfinite⟩ := hcompact.elim_finite_subcover domains hopen hcover
  have hfinite_nonempty : finite.Nonempty := by
    obtain ⟨level, hlevel⟩ := hnonempty
    obtain ⟨pair, hpair⟩ := Set.mem_iUnion.mp (hfinite hlevel)
    obtain ⟨hmem, _⟩ := Set.mem_iUnion.mp hpair
    exact ⟨pair, hmem⟩
  refine ⟨finite.image Prod.fst, finite.inf' hfinite_nonempty (fun pair => pair.2.val),
    ⋃ pair ∈ finite, domains pair, ?_, ?_, hfinite, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun pair _ => pair.2.property)
  · exact isOpen_biUnion (fun pair _ => hopen pair)
  · intro level hlevel
    obtain ⟨pair, hpair⟩ := Set.mem_iUnion.mp hlevel
    obtain ⟨hmem, hdomain⟩ := Set.mem_iUnion.mp hpair
    refine ⟨pair.1, Finset.mem_image.mpr ⟨pair, hmem, rfl⟩, ?_⟩
    exact lt_of_le_of_lt (Finset.inf'_le _ hmem) hdomain

/-- A finite family of selected return words has a common maximum depth. -/
theorem selected_depth_le_max {ι : Type*} (selected : Finset ι) (depth : ι → ℕ)
    {index : ι} (hindex : index ∈ selected) : depth index ≤ selected.sup depth :=
  Finset.le_sup hindex

end LambdaCantor.Last


