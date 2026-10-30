import LambdaCantor.Classical.Rational
import LambdaCantor.Classical.NoIsolation

/-! Independently compilable Definition2.1, Lemma2.2 and Proposition2.4
wrappers for manuscript429d53b. No Section3.1 production data are imported. -/
noncomputable section
namespace LambdaCantor.Manuscript

/-- Definition 2.1: the Cantor set called C in the circle construction. -/
abbrev classicalCantor : Set ℝ := cantorSet (1/3)

/-- Definition 2.1: the circle intersection called E. -/
abbrev classicalCircle : Set (ℝ × ℝ) := intersection 2 (1/3)

/-- Lemma 2.2 with both directions of the rational-point classification. -/
theorem rational_classical_circle (first second : ℚ) :
    ((first : ℝ), (second : ℝ)) ∈ classicalCircle ↔
      (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) := by
  constructor
  · intro member
    exact Classical.rational_circle_axes first second member.1 member.2.1
      (by simpa only [Real.rpow_two] using member.2.2)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simpa only [Rat.cast_zero, Rat.cast_one] using
        (show ((0 : ℝ), (1 : ℝ)) ∈ classicalCircle from
          ⟨zero_mem_cantorSet _, one_mem_cantorSet (by norm_num) (by norm_num), by norm_num⟩)
    · simpa only [Rat.cast_zero, Rat.cast_one] using
        (show ((1 : ℝ), (0 : ℝ)) ∈ classicalCircle from
          ⟨one_mem_cantorSet (by norm_num) (by norm_num), zero_mem_cantorSet _, by norm_num⟩)

/-- Proposition 2.4, with both parts of the statement together. -/
theorem classical_source_nonempty_compact :
    Classical.source.Nonempty ∧ IsCompact Classical.source :=
  ⟨Classical.source_nonempty, Classical.source_compact⟩

end LambdaCantor.Manuscript

#print axioms LambdaCantor.Manuscript.rational_classical_circle
#print axioms LambdaCantor.Manuscript.classical_source_nonempty_compact
