import LambdaCantor.Last.AnalyticCoarseShallowGaps
import LambdaCantor.Last.AnalyticCoarseThreeGapExclusion

noncomputable section
namespace LambdaCantor.Last

private theorem scaled_divided_gap_bound
    {period exponent width gapLeft gapRight gapRatio : ℝ}
    (hperiod : 0 < period) (hexponent : 0 ≤ exponent)
    (hgap : gapRight - gapLeft ≤ gapRatio * width) :
    exponent * gapRight / period - exponent * gapLeft / period ≤
      gapRatio * exponent * (width / period) := by
  calc
    _ = exponent * (gapRight - gapLeft) / period := by ring
    _ ≤ exponent * (gapRatio * width) / period :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hexponent) hperiod.le
    _ = _ := by ring

private theorem coarse_divided_empty_arc_in_three_gaps
    {ratio exponent period normalizedHull : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent : 0 < exponent) (hexponent_upper : exponent ≤ 20)
    (hperiod : 0 < period)
    (hcancel : normalizedHull * period = -Real.log (1 - ratio))
    (left : ℝ) (hleft : -exponent * normalizedHull ≤ left)
    (hright : left + normalizedHull ≤ 0)
    (hempty : ∀ point ∈ (fun value => exponent * value / period) '' coarseOuterLogSet ratio,
      point ∉ Set.Ioo left (left + normalizedHull)) :
    (exponent * Real.log (1 - ratio + ratio ^ 2) / period ≤ left ∧
      left + normalizedHull ≤ exponent * Real.log (1 - ratio ^ 2) / period) ∨
    (exponent * Real.log (1 - ratio + ratio ^ 3) / period ≤ left ∧
      left + normalizedHull ≤ exponent * Real.log ((1 - ratio) * (1 + ratio ^ 2)) / period) ∨
    (exponent * Real.log (1 - ratio ^ 2 + ratio ^ 3) / period ≤ left ∧
      left + normalizedHull ≤ exponent * Real.log (1 - ratio ^ 3) / period) := by
  have hactual_left : exponent * Real.log (1 - ratio) ≤ period * left := by
    have hscaled := mul_le_mul_of_nonneg_right hleft hperiod.le
    have hscaled_cancel := congrArg (fun value : ℝ => exponent * value) hcancel
    nlinarith only [hscaled, hscaled_cancel]
  have hactual_right : period * (left + normalizedHull) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hperiod.le hright
  have hactual_width : period * (left + normalizedHull) - period * left =
      -Real.log (1 - ratio) := by
    nlinarith only [hcancel]
  have hcases := coarse_scaled_empty_arc_in_three_gaps hlower hupper
    hexponent hexponent_upper hactual_left hactual_right hactual_width (by
      intro value hvalue hinside
      apply hempty (exponent * value / period) ⟨value, hvalue, rfl⟩
      constructor
      · exact (lt_div_iff₀ hperiod).mpr (by simpa only [mul_comm] using hinside.1)
      · exact (div_lt_iff₀ hperiod).mpr (by simpa only [mul_comm] using hinside.2))
  rcases hcases with hroot | hleft_child | hright_child
  · exact Or.inl ⟨(div_le_iff₀ hperiod).mpr (by simpa only [mul_comm] using hroot.1),
      (le_div_iff₀ hperiod).mpr (by simpa only [mul_comm] using hroot.2)⟩
  · exact Or.inr (Or.inl
      ⟨(div_le_iff₀ hperiod).mpr (by simpa only [mul_comm] using hleft_child.1),
        (le_div_iff₀ hperiod).mpr (by simpa only [mul_comm] using hleft_child.2)⟩)
  · exact Or.inr (Or.inr
      ⟨(div_le_iff₀ hperiod).mpr (by simpa only [mul_comm] using hright_child.1),
        (le_div_iff₀ hperiod).mpr (by simpa only [mul_comm] using hright_child.2)⟩)

theorem coarse_strict_log_link_capacity_range {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent_lower : 6 ≤ exponent) (hexponent_upper : exponent ≤ 20) :
    CoarseStrictLogLink ratio exponent := by
  let period := -Real.log ratio
  let width := -Real.log (1 - ratio)
  let normalizedHull := width / period
  let arcLeft := (Real.log exponent + Real.log (1 - ratio)) / period
  have hratio : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hexponent : 0 < exponent := by linarith
  have hperiod : 0 < period := neg_pos.mpr (Real.log_neg hratio hless)
  have hcancel : normalizedHull * period = width := div_mul_cancel₀ _ hperiod.ne'
  have hnumeric := coarse_log_hull_period_bounds hlower hupper
  have hnormalized_lower : 453 / 1000 < normalizedHull := hnumeric.2.2.1
  have hnormalized_upper : normalizedHull < 1 := hnumeric.2.2.2
  have hone : 0 < 1 - ratio := by linarith
  have hsquare : ratio ^ 2 < 1 := by nlinarith only [hratio, hless]
  have hcube : ratio ^ 3 < 1 := by
    have := mul_lt_mul_of_pos_left hsquare hratio
    nlinarith only [this, hless]
  rcases coarse_three_log_gap_bounds hlower hupper with ⟨hfirst, hsecond, hthird⟩
  rw [Real.log_div (sub_pos.mpr hsquare).ne'
    (ne_of_gt (show 0 < 1 - ratio + ratio ^ 2 by positivity))] at hfirst
  rw [Real.log_div (ne_of_gt (mul_pos hone (by positivity : 0 < 1 + ratio ^ 2)))
    (ne_of_gt (show 0 < 1 - ratio + ratio ^ 3 by positivity))] at hsecond
  rw [Real.log_div (sub_pos.mpr hcube).ne'
    (ne_of_gt (show 0 < 1 - ratio ^ 2 + ratio ^ 3 by positivity))] at hthird
  by_contra hnot
  have hexclusion := coarse_three_gap_periodic_exclusion
    (set := (fun value => exponent * value / period) '' coarseOuterLogSet ratio)
    (arcLeft := arcLeft) hexponent_lower hnormalized_lower hnormalized_upper
    (scaled_divided_gap_bound hperiod hexponent.le hfirst.le)
    (scaled_divided_gap_bound hperiod hexponent.le hsecond.le)
    (scaled_divided_gap_bound hperiod hexponent.le hthird.le)
    (coarse_divided_empty_arc_in_three_gaps hlower hupper hexponent hexponent_upper
      hperiod hcancel)
  apply hexclusion
  rintro _ ⟨value, hvalue, rfl⟩ shift hinside
  have hright_eq : arcLeft + normalizedHull = Real.log exponent / period := by
    dsimp [arcLeft, normalizedHull, width]
    ring
  rw [hright_eq] at hinside
  have hleft_mul : Real.log exponent + Real.log (1 - ratio) <
      (exponent * value / period + (shift : ℝ) * 1) * period :=
    (div_lt_iff₀ hperiod).mp hinside.1
  have hright_mul := (lt_div_iff₀ hperiod).mp hinside.2
  have hvalue_cancel := div_mul_cancel₀ (exponent * value) hperiod.ne'
  apply hnot
  refine ⟨shift, value, hvalue, ?_⟩
  dsimp [period] at hleft_mul hright_mul hvalue_cancel
  constructor <;> nlinarith only [hleft_mul, hright_mul, hvalue_cancel]

end LambdaCantor.Last
