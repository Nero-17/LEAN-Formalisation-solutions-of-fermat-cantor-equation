import LambdaCantor.Last.AnalyticCoarseLogGapGeometry
import LambdaCantor.Last.AnalyticCoarsePeriodicIntervals

noncomputable section
namespace LambdaCantor.Last

theorem coarse_scaled_empty_interval_in_gap {ratio exponent left right : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent : 0 < exponent)
    (hleft : exponent * Real.log (1 - ratio) ≤ left) (hright : right ≤ 0)
    (horder : left < right)
    (hempty : ∀ value ∈ coarseOuterLogSet ratio,
      exponent * value ∉ Set.Ioo left right) :
    ∃ word : List Bool,
      exponent * coarseLogNode ratio word ratio ≤ left ∧
        right ≤ exponent * coarseLogNode ratio word (1 - ratio) := by
  have hleft_div : Real.log (1 - ratio) ≤ left / exponent := by
    apply (le_div_iff₀ hexponent).mpr
    simpa only [mul_comm] using hleft
  have hright_div : right / exponent ≤ 0 := div_nonpos_of_nonpos_of_nonneg hright hexponent.le
  have horder_div : left / exponent < right / exponent :=
    div_lt_div_of_pos_right horder hexponent
  obtain ⟨word, hfirst, hsecond⟩ := coarse_log_empty_interval_in_gap
    hlower hupper hleft_div hright_div horder_div (by
      intro value hvalue hinside
      apply hempty value hvalue
      constructor
      · have := (div_lt_iff₀ hexponent).mp hinside.1
        nlinarith
      · have := (lt_div_iff₀ hexponent).mp hinside.2
        nlinarith)
  refine ⟨word, ?_, ?_⟩
  · have := (le_div_iff₀ hexponent).mp hfirst
    nlinarith
  · have := (div_le_iff₀ hexponent).mp hsecond
    nlinarith

/-- Failure of the desired strict connection produces an actual empty arc,
translated wholly inside the scaled logarithmic hull. -/
theorem coarse_scaled_empty_arc_of_not_link {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hcover : -Real.log ratio <
      (-Real.log (1 - ratio)) - exponent * Real.log (1 - ratio))
    (hnot : ¬ CoarseStrictLogLink ratio exponent) :
    ∃ arcLeft : ℝ,
      exponent * Real.log (1 - ratio) ≤ arcLeft ∧
      arcLeft + (-Real.log (1 - ratio)) ≤ 0 ∧
      PeriodicSetAvoids ((fun value => exponent * value) '' coarseOuterLogSet ratio)
        (-Real.log ratio) arcLeft (arcLeft + (-Real.log (1 - ratio))) := by
  have hratio : 0 ≤ ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hperiod : 0 < -Real.log ratio := neg_pos.mpr
    (Real.log_neg (by linarith) hless)
  have hzero : (0 : ℝ) ∈
      (fun value => exponent * value) '' coarseOuterLogSet ratio := by
    exact ⟨0, zero_mem_coarseOuterLogSet hratio hless, mul_zero exponent⟩
  have hendpoint : exponent * Real.log (1 - ratio) ∈
      (fun value => exponent * value) '' coarseOuterLogSet ratio :=
    ⟨Real.log (1 - ratio), lower_mem_coarseOuterLogSet ratio, rfl⟩
  have hempty : PeriodicSetAvoids
      ((fun value => exponent * value) '' coarseOuterLogSet ratio)
      (-Real.log ratio) (Real.log exponent + Real.log (1 - ratio))
      (Real.log exponent + Real.log (1 - ratio) + (-Real.log (1 - ratio))) := by
    rintro _ ⟨value, hvalue, rfl⟩ shift hinside
    apply hnot
    refine ⟨shift, value, hvalue, ?_⟩
    constructor <;> linarith [hinside.1, hinside.2]
  obtain ⟨shift, hleft, hright, htranslated⟩ :=
    periodic_empty_arc_in_hull hperiod hzero hendpoint hcover hempty
  refine ⟨Real.log exponent + Real.log (1 - ratio) -
    (shift : ℝ) * (-Real.log ratio), hleft, ?_, ?_⟩
  · linarith
  · convert htranslated using 1 <;> ring

end LambdaCantor.Last
