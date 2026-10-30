import LambdaCantor.Last.ExternalNewhouseBinary
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last.ExternalNewhouse

theorem BinaryGapPresentation.child_subset {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (word : List Bool) (digit : Bool) :
    Set.Icc (presentation.left (word ++ [digit])) (presentation.right (word ++ [digit])) ⊆
      Set.Icc (presentation.left word) (presentation.right word) := by
  intro point hpoint
  obtain ⟨hleft, hgap, hright⟩ := presentation.children_order word
  cases digit
  · rw [presentation.left_coherent] at hpoint
    exact ⟨hpoint.1, hpoint.2.trans (hgap.le.trans hright.le)⟩
  · rw [presentation.right_coherent] at hpoint
    exact ⟨(hleft.le.trans hgap.le).trans hpoint.1, hpoint.2⟩

theorem BinaryGapPresentation.append_subset {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (word rest : List Bool) :
    Set.Icc (presentation.left (word ++ rest)) (presentation.right (word ++ rest)) ⊆
      Set.Icc (presentation.left word) (presentation.right word) := by
  induction rest using List.reverseRecOn with
  | nil => simp
  | append_singleton rest digit induction =>
    simpa only [List.append_assoc] using
      (presentation.child_subset (word ++ rest) digit).trans induction

theorem BinaryGapPresentation.node_subset_root {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (word : List Bool) :
    Set.Icc (presentation.left word) (presentation.right word) ⊆
      Set.Icc (presentation.left []) (presentation.right []) := by
  simpa only [List.nil_append] using presentation.append_subset [] word

theorem BinaryGapPresentation.subset_root {set : Set ℝ}
    (presentation : BinaryGapPresentation set) :
    set ⊆ Set.Icc (presentation.left []) (presentation.right []) := by
  intro point hpoint
  rw [presentation.limit_set] at hpoint
  obtain ⟨word, hlength, hbounds⟩ := hpoint 0
  have hnil : word = [] := by
    cases word with
    | nil => rfl
    | cons digit rest => simp at hlength
  simpa only [hnil] using hbounds

theorem BinaryGapPresentation.left_mem_root {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (word : List Bool) :
    presentation.left word ∈ Set.Icc (presentation.left []) (presentation.right []) :=
  presentation.node_subset_root word ⟨le_rfl, (presentation.node_order word).le⟩

theorem BinaryGapPresentation.right_mem_root {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (word : List Bool) :
    presentation.right word ∈ Set.Icc (presentation.left []) (presentation.right []) :=
  presentation.node_subset_root word ⟨(presentation.node_order word).le, le_rfl⟩

/-- Every actual complementary point in the hull belongs to one of the
explicit binary gaps. No sorting of gaps or thickness theorem is used. -/
theorem BinaryGapPresentation.exists_gap {set : Set ℝ}
    (presentation : BinaryGapPresentation set) {point : ℝ}
    (hpoint : point ∈ Set.Icc (presentation.left []) (presentation.right []))
    (houtside : point ∉ set) :
    ∃ word : List Bool, point ∈ Set.Ioo
      (presentation.right (word ++ [false])) (presentation.left (word ++ [true])) := by
  classical
  have hfailure : ∃ depth : ℕ, ¬ ∃ word : List Bool,
      word.length = depth ∧ point ∈ Set.Icc (presentation.left word) (presentation.right word) := by
    by_contra hfailure
    push_neg at hfailure
    apply houtside
    rw [presentation.limit_set]
    exact hfailure
  have hspec := Nat.find_spec hfailure
  have hnonzero : Nat.find hfailure ≠ 0 := by
    intro hzero
    rw [hzero] at hspec
    exact hspec ⟨[], rfl, hpoint⟩
  have hprevious : ∃ word : List Bool, word.length = Nat.find hfailure - 1 ∧
      point ∈ Set.Icc (presentation.left word) (presentation.right word) := by
    by_contra hprevious
    exact Nat.find_min hfailure (by omega) hprevious
  obtain ⟨word, hlength, hbounds⟩ := hprevious
  have hfalse : point ∉ Set.Icc
      (presentation.left (word ++ [false])) (presentation.right (word ++ [false])) := by
    intro hchild
    apply hspec
    exact ⟨word ++ [false], by simp only [List.length_append, List.length_singleton]; omega, hchild⟩
  have htrue : point ∉ Set.Icc
      (presentation.left (word ++ [true])) (presentation.right (word ++ [true])) := by
    intro hchild
    apply hspec
    exact ⟨word ++ [true], by simp only [List.length_append, List.length_singleton]; omega, hchild⟩
  refine ⟨word, ?_, ?_⟩
  · by_contra hless
    apply hfalse
    exact ⟨by rw [presentation.left_coherent]; exact hbounds.1, le_of_not_gt hless⟩
  · by_contra hless
    apply htrue
    exact ⟨le_of_not_gt hless, by rw [presentation.right_coherent]; exact hbounds.2⟩

end LambdaCantor.Last.ExternalNewhouse
