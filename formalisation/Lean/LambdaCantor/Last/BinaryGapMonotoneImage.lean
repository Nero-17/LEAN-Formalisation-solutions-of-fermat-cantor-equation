import LambdaCantor.Last.BinaryGapBasics
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last.ExternalNewhouse

def BinaryGapPresentation.monotoneImage {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (function : ℝ → ℝ) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hcontinuous : ContinuousOn function (Set.Icc (presentation.left []) (presentation.right [])))
    (hincrements : ∀ first ∈ Set.Icc (presentation.left []) (presentation.right []),
      ∀ second ∈ Set.Icc (presentation.left []) (presentation.right []), first ≤ second →
        lower * (second - first) ≤ function second - function first ∧
          function second - function first ≤ upper * (second - first)) :
    BinaryGapPresentation (function '' set) := by
  have hstrict : StrictMonoOn function (Set.Icc (presentation.left []) (presentation.right [])) := by
    intro first hfirst second hsecond hless
    have hbound := (hincrements first hfirst second hsecond hless.le).1
    have hpositive := mul_pos hlower (sub_pos.mpr hless)
    linarith
  refine {
    left := fun word => function (presentation.left word)
    right := fun word => function (presentation.right word)
    node_order := fun word => hstrict (presentation.left_mem_root word)
      (presentation.right_mem_root word) (presentation.node_order word)
    left_coherent := by intro word; rw [presentation.left_coherent]
    right_coherent := by intro word; rw [presentation.right_coherent]
    children_order := ?_
    limit_set := ?_
    mesh := ?_
  }
  · intro word
    obtain ⟨hfirst, hgap, hsecond⟩ := presentation.children_order word
    exact ⟨hstrict (presentation.left_mem_root word)
        (presentation.right_mem_root (word ++ [false])) hfirst,
      hstrict (presentation.right_mem_root (word ++ [false]))
        (presentation.left_mem_root (word ++ [true])) hgap,
      hstrict (presentation.left_mem_root (word ++ [true]))
        (presentation.right_mem_root word) hsecond⟩
  · ext point
    constructor
    · rintro ⟨original, hmem, rfl⟩ depth
      have hroot := presentation.subset_root hmem
      rw [presentation.limit_set] at hmem
      obtain ⟨word, hlength, hbounds⟩ := hmem depth
      exact ⟨word, hlength,
        hstrict.monotoneOn (presentation.left_mem_root word) hroot hbounds.1,
        hstrict.monotoneOn hroot (presentation.right_mem_root word) hbounds.2⟩
    · intro hlevels
      obtain ⟨initial, hlength, hroot_image⟩ := hlevels 0
      have hnil : initial = [] := by
        cases initial with
        | nil => rfl
        | cons digit rest => simp at hlength
      rw [hnil] at hroot_image
      obtain ⟨original, hroot, hequation⟩ :=
        intermediate_value_Icc (presentation.node_order []).le hcontinuous hroot_image
      refine ⟨original, ?_, hequation⟩
      rw [presentation.limit_set]
      intro depth
      obtain ⟨word, hword_length, hbounds⟩ := hlevels depth
      refine ⟨word, hword_length, ?_, ?_⟩
      · by_contra hless
        have hvalue := hstrict hroot (presentation.left_mem_root word) (lt_of_not_ge hless)
        rw [hequation] at hvalue
        exact (not_lt_of_ge hbounds.1) hvalue
      · by_contra hless
        have hvalue := hstrict (presentation.right_mem_root word) hroot (lt_of_not_ge hless)
        rw [hequation] at hvalue
        exact (not_lt_of_ge hbounds.2) hvalue
  · intro epsilon hepsilon
    obtain ⟨depth, hdepth⟩ := presentation.mesh (epsilon / upper) (div_pos hepsilon hupper)
    refine ⟨depth, ?_⟩
    intro word hword
    have hbound := (hincrements (presentation.left word) (presentation.left_mem_root word)
      (presentation.right word) (presentation.right_mem_root word) (presentation.node_order word).le).2
    have hsmall := mul_lt_mul_of_pos_left (hdepth word hword) hupper
    have hcancel : upper * (epsilon / upper) = epsilon := by field_simp [hupper.ne']
    linarith

theorem BinaryGapPresentation.monotoneImage_bridgeBound {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (function : ℝ → ℝ) {lower upper bound : ℝ}
    (hlower : 0 < lower) (hupper : 0 < upper) (hbound_nonnegative : 0 ≤ bound)
    (hcontinuous : ContinuousOn function (Set.Icc (presentation.left []) (presentation.right [])))
    (hincrements : ∀ first ∈ Set.Icc (presentation.left []) (presentation.right []),
      ∀ second ∈ Set.Icc (presentation.left []) (presentation.right []), first ≤ second →
        lower * (second - first) ≤ function second - function first ∧
          function second - function first ≤ upper * (second - first))
    (hbridges : presentation.bridgeBound bound) :
    (presentation.monotoneImage function hlower hupper hcontinuous hincrements).bridgeBound
      (bound * lower / upper) := by
  intro word
  have hchildren := presentation.children_order word
  have hgap := (hincrements (presentation.right (word ++ [false]))
    (presentation.right_mem_root _) (presentation.left (word ++ [true]))
    (presentation.left_mem_root _) hchildren.2.1.le).2
  have hleft := (hincrements (presentation.left word) (presentation.left_mem_root _)
    (presentation.right (word ++ [false])) (presentation.right_mem_root _) hchildren.1.le).1
  have hright := (hincrements (presentation.left (word ++ [true])) (presentation.left_mem_root _)
    (presentation.right word) (presentation.right_mem_root _) hchildren.2.2.le).1
  have hscaled_gap := mul_le_mul_of_nonneg_left hgap
    (div_nonneg (mul_nonneg hbound_nonnegative hlower.le) hupper.le)
  have hcancel : bound * lower / upper *
      (upper * (presentation.left (word ++ [true]) - presentation.right (word ++ [false]))) =
      lower * (bound * (presentation.left (word ++ [true]) - presentation.right (word ++ [false]))) := by
    field_simp [hupper.ne']
    <;> ring
  rw [hcancel] at hscaled_gap
  change bound * lower / upper *
      (function (presentation.left (word ++ [true])) - function (presentation.right (word ++ [false]))) ≤
        function (presentation.right (word ++ [false])) - function (presentation.left word) ∧
    bound * lower / upper *
      (function (presentation.left (word ++ [true])) - function (presentation.right (word ++ [false]))) ≤
        function (presentation.right word) - function (presentation.left (word ++ [true]))
  exact ⟨hscaled_gap.trans ((mul_le_mul_of_nonneg_left (hbridges word).1 hlower.le).trans hleft),
    hscaled_gap.trans ((mul_le_mul_of_nonneg_left (hbridges word).2 hlower.le).trans hright)⟩

end LambdaCantor.Last.ExternalNewhouse
