import LambdaCantor.Last.AnalyticCoarseScaledGaps

noncomputable section
namespace LambdaCantor.Last

theorem coarse_strict_log_link_second_range {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent_lower : 23 / 19 ≤ exponent) (hexponent_upper : exponent ≤ 3) :
    CoarseStrictLogLink ratio exponent := by
  have hratio : 0 < ratio := by linarith
  have hexponent : 0 < exponent := by linarith
  have hhull := (coarse_log_hull_period_bounds hlower hupper).1
  have hperiod := (coarse_log_hull_period_bounds hlower hupper).2.1
  have hhull_positive : 0 < -Real.log (1 - ratio) := by linarith
  have hscaled_hull := mul_le_mul_of_nonneg_right hexponent_lower hhull_positive.le
  have hcover : -Real.log ratio <
      (-Real.log (1 - ratio)) - exponent * Real.log (1 - ratio) := by
    nlinarith
  by_contra hnot
  obtain ⟨arcLeft, hleft, hright, hempty⟩ :=
    coarse_scaled_empty_arc_of_not_link hlower hupper hcover hnot
  obtain ⟨word, hgap_left, hgap_right⟩ := coarse_scaled_empty_interval_in_gap
    hlower hupper hexponent hleft hright
    (show arcLeft < arcLeft + (-Real.log (1 - ratio)) by linarith) (by
      intro value hvalue hinside
      apply hempty (exponent * value) ⟨value, hvalue, rfl⟩ 0
      simpa only [Int.cast_zero, zero_mul, add_zero] using hinside)
  have hgap_large : -Real.log (1 - ratio) ≤ exponent *
      (coarseLogNode ratio word (1 - ratio) - coarseLogNode ratio word ratio) := by
    nlinarith
  by_cases hroot : word = []
  · subst word
    have hnum : 0 < 1 - ratio ^ 2 := by nlinarith
    have hden : 0 < 1 - ratio + ratio ^ 2 :=
      add_pos_of_pos_of_nonneg
        (sub_pos.mpr (hupper.trans (by norm_num : (1 / 2 : ℝ) < 1))) (sq_nonneg ratio)
    have hroot_bound := coarse_root_log_gap_lt_rational hlower hupper
    rw [Real.log_div hnum.ne' hden.ne'] at hroot_bound
    have hidentity : coarseLogNode ratio [] (1 - ratio) - coarseLogNode ratio [] ratio =
        Real.log (1 - ratio ^ 2) - Real.log (1 - ratio + ratio ^ 2) := by
      simp only [coarseLogNode, coarseRawNode, scalarWordMap]
      congr 2 <;> ring
    rw [hidentity] at hgap_large
    have hscaled := mul_lt_mul_of_pos_left hroot_bound hexponent
    nlinarith
  · have hdepth : 1 ≤ word.length := by
      have := List.length_pos_iff.mpr hroot
      omega
    have hsmall := coarseLogNode_nonroot_gap_lt hratio hupper word hdepth
    have hscaled := mul_lt_mul_of_pos_left hsmall hexponent
    nlinarith

end LambdaCantor.Last
