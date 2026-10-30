import LambdaCantor.Last.AnalyticCoarseScaledGaps

noncomputable section
namespace LambdaCantor.Last

theorem coarseLogNode_shallow_gap_values (ratio : ℝ) :
    coarseLogNode ratio [] ratio = Real.log (1 - ratio + ratio ^ 2) ∧
    coarseLogNode ratio [] (1 - ratio) = Real.log (1 - ratio ^ 2) ∧
    coarseLogNode ratio [false] ratio = Real.log (1 - ratio + ratio ^ 3) ∧
    coarseLogNode ratio [false] (1 - ratio) = Real.log ((1 - ratio) * (1 + ratio ^ 2)) ∧
    coarseLogNode ratio [true] ratio = Real.log (1 - ratio ^ 2 + ratio ^ 3) ∧
    coarseLogNode ratio [true] (1 - ratio) = Real.log (1 - ratio ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [coarseLogNode, coarseRawNode, scalarWordMap,
      Bool.false_eq_true, if_false, if_true] <;> congr 1 <;> ring

/-- Up to exponent twenty, any empty arc of hull width must lie in the root
gap or one of its two children. All deeper actual gaps are strictly shorter. -/
theorem coarse_scaled_empty_arc_in_three_gaps {ratio exponent left right : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent : 0 < exponent) (hexponent_upper : exponent ≤ 20)
    (hleft : exponent * Real.log (1 - ratio) ≤ left) (hright : right ≤ 0)
    (hwidth : right - left = -Real.log (1 - ratio))
    (hempty : ∀ value ∈ coarseOuterLogSet ratio,
      exponent * value ∉ Set.Ioo left right) :
    (exponent * Real.log (1 - ratio + ratio ^ 2) ≤ left ∧
      right ≤ exponent * Real.log (1 - ratio ^ 2)) ∨
    (exponent * Real.log (1 - ratio + ratio ^ 3) ≤ left ∧
      right ≤ exponent * Real.log ((1 - ratio) * (1 + ratio ^ 2))) ∨
    (exponent * Real.log (1 - ratio ^ 2 + ratio ^ 3) ≤ left ∧
      right ≤ exponent * Real.log (1 - ratio ^ 3)) := by
  have hhull := (coarse_log_hull_period_bounds hlower hupper).1
  obtain ⟨word, hgap_left, hgap_right⟩ := coarse_scaled_empty_interval_in_gap
    hlower hupper hexponent hleft hright (by linarith) hempty
  rcases coarseLogNode_shallow_gap_values ratio with
    ⟨hroot_left, hroot_right, hfalse_left, hfalse_right, htrue_left, htrue_right⟩
  cases word with
  | nil =>
      exact Or.inl ⟨by simpa only [hroot_left] using hgap_left,
        by simpa only [hroot_right] using hgap_right⟩
  | cons digit rest =>
      cases rest with
      | nil =>
          cases digit with
          | false =>
              exact Or.inr (Or.inl ⟨by simpa only [hfalse_left] using hgap_left,
                by simpa only [hfalse_right] using hgap_right⟩)
          | true =>
              exact Or.inr (Or.inr ⟨by simpa only [htrue_left] using hgap_left,
                by simpa only [htrue_right] using hgap_right⟩)
      | cons next tail =>
          have hdeep := coarseLogNode_deep_gap_lt hlower hupper (digit :: next :: tail)
            (by simp)
          have hscaled := mul_lt_mul_of_pos_left hdeep hexponent
          have hhull_positive : 0 < -Real.log (1 - ratio) := by linarith
          have hbound := mul_le_mul_of_nonneg_right hexponent_upper
            (div_nonneg hhull_positive.le (by norm_num : (0 : ℝ) ≤ 20))
          exfalso
          nlinarith

end LambdaCantor.Last
