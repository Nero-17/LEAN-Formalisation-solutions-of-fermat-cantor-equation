import LambdaCantor.Common

noncomputable section
namespace LambdaCantor

/-- Every positive-dimensional admissible fibre bounds the first transition. -/
theorem firstTransition_le_of_positive {exponent ratio : ℝ}
    (hratio : ratio ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hpositive : 0 < dimH (intersection exponent ratio)) :
    firstTransition exponent ≤ ratio := by
  apply csInf_le
  · exact ⟨0, fun _ h => le_of_lt h.1.1⟩
  · exact ⟨hratio, hpositive⟩

/-- Source Theorem irrational-onset: the order-theoretic deduction, with its
    two substantive preceding results retained as explicit hypotheses. -/
theorem firstTransition_eq_quarter_of_nearby {exponent : ℝ}
    (hlower : (1 : ℝ) / 4 ≤ firstTransition exponent)
    (hnearby : ∀ upper : ℝ, 1 / 4 < upper → upper < 1 / 2 →
      ∃ ratio ∈ Set.Ioo (1 / 4 : ℝ) upper,
        0 < dimH (intersection exponent ratio)) :
    firstTransition exponent = 1 / 4 := by
  apply le_antisymm _ hlower
  by_contra h
  have hgap : (1 : ℝ) / 4 < firstTransition exponent := lt_of_not_ge h
  obtain ⟨ratio, hratio, hpositive⟩ :=
    hnearby (min (firstTransition exponent) (3 / 8))
      (lt_min hgap (by norm_num))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  have hle := firstTransition_le_of_positive
    (exponent := exponent) (ratio := ratio)
    (show ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) from
      ⟨by linarith [hratio.1],
       le_trans (le_of_lt hratio.2) (le_trans (min_le_right _ _) (by norm_num))⟩)
    hpositive
  exact (not_lt_of_ge hle) (lt_of_lt_of_le hratio.2 (min_le_left _ _))

/-- A nonzero restricted measure gives at least one element of its carrier. -/
theorem nonempty_of_measure_ne_zero {α : Type*} [MeasurableSpace α]
    (measure : MeasureTheory.Measure α) (set : Set α)
    (hmeasure : measure set ≠ 0) : set.Nonempty := by
  by_contra h
  have : set = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  simp [this] at hmeasure

end LambdaCantor
