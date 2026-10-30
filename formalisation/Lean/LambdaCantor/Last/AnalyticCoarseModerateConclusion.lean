import LambdaCantor.Last.AnalyticCoarseScaledGaps
import LambdaCantor.Last.AnalyticCoarseModerateData
import LambdaCantor.Last.AnalyticCoarsePeriodicRoot

noncomputable section
namespace LambdaCantor.Last

theorem coarse_scaled_empty_root_gap {ratio exponent left right : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent_lower : 3 ≤ exponent) (hexponent_upper : exponent ≤ 6)
    (hleft : exponent * Real.log (1 - ratio) ≤ left) (hright : right ≤ 0)
    (hwidth : right - left = -Real.log (1 - ratio))
    (hempty : ∀ value ∈ coarseOuterLogSet ratio,
      exponent * value ∉ Set.Ioo left right) :
    exponent * Real.log (1 - ratio + ratio ^ 2) ≤ left ∧
      right ≤ exponent * Real.log (1 - ratio ^ 2) := by
  have hratio : 0 < ratio := by linarith
  have hexponent : 0 < exponent := by linarith
  have hhull := (coarse_log_hull_period_bounds hlower hupper).1
  obtain ⟨word, hgap_left, hgap_right⟩ := coarse_scaled_empty_interval_in_gap
    hlower hupper hexponent hleft hright (by linarith) hempty
  by_cases hroot : word = []
  · subst word
    have hfirst : coarseLogNode ratio [] ratio = Real.log (1 - ratio + ratio ^ 2) := by
      simp only [coarseLogNode, coarseRawNode, scalarWordMap]
      congr 1 <;> ring
    have hsecond : coarseLogNode ratio [] (1 - ratio) = Real.log (1 - ratio ^ 2) := by
      simp only [coarseLogNode, coarseRawNode, scalarWordMap]
      congr 1 <;> ring
    simpa only [hfirst, hsecond] using And.intro hgap_left hgap_right
  · have hdepth : 1 ≤ word.length := by
      have := List.length_pos_iff.mpr hroot
      omega
    have hsmall := mul_lt_mul_of_pos_left
      (coarseLogNode_nonroot_gap_lt hratio hupper word hdepth) hexponent
    have hdata := (coarse_moderate_root_data hlower hupper).2.2.2.2
      exponent hexponent_lower hexponent_upper
    dsimp [coarseLogHullLength] at hdata
    nlinarith [hdata.2.2]

theorem coarse_strict_log_link_moderate_range {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent_lower : 3 ≤ exponent) (hexponent_upper : exponent ≤ 6) :
    CoarseStrictLogLink ratio exponent := by
  have hratio : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hhull := (coarse_log_hull_period_bounds hlower hupper).1
  have hperiod : 0 < -Real.log ratio := neg_pos.mpr (Real.log_neg hratio hless)
  rcases coarse_moderate_root_data hlower hupper with
    ⟨hgap, hbridge, hdifference, hproduct, hmoderate⟩
  have hdata := hmoderate exponent hexponent_lower hexponent_upper
  have hcover : -Real.log ratio <
      (-Real.log (1 - ratio)) - exponent * Real.log (1 - ratio) := by
    dsimp [coarseLogPeriodLength, coarseLogHullLength] at hdata
    nlinarith [hdata.1]
  by_contra hnot
  obtain ⟨arcLeft, hleft, hright, hempty⟩ :=
    coarse_scaled_empty_arc_of_not_link hlower hupper hcover hnot
  apply periodic_root_gap_contradiction
    (set := (fun value => exponent * value) '' coarseOuterLogSet ratio)
    (exponent := exponent) (period := -Real.log ratio)
    (width := -Real.log (1 - ratio))
    (gapLeft := exponent * Real.log (1 - ratio + ratio ^ 2))
    (gapRight := exponent * Real.log (1 - ratio ^ 2))
    (gapLength := coarseLogRootGapLength ratio)
    (bridgeLength := coarseLogRootRightBridge ratio)
    hperiod (by linarith) hgap hbridge
    (by
      refine ⟨Real.log (1 - ratio), lower_mem_coarseOuterLogSet ratio, ?_⟩
      ring)
    (by dsimp [coarseLogRootGapLength]; ring)
    (by dsimp [coarseLogRootRightBridge]; ring)
    (by simpa only [coarseLogPeriodLength, coarseLogHullLength] using hdata.2.1)
    (by simpa only [coarseLogPeriodLength, coarseLogHullLength] using hproduct)
    (by
      intro left hleft hright havoid
      apply coarse_scaled_empty_root_gap hlower hupper hexponent_lower hexponent_upper
        (by nlinarith) hright (by ring)
      intro value hvalue hinside
      apply havoid (exponent * value) ⟨value, hvalue, rfl⟩ 0
      simpa only [Int.cast_zero, zero_mul, add_zero] using hinside)
    (by nlinarith) hright hempty

end LambdaCantor.Last
