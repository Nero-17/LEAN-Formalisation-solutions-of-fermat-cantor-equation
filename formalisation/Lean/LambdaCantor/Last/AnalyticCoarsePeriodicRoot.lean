import LambdaCantor.Last.AnalyticCoarsePeriodicIntervals

noncomputable section
namespace LambdaCantor.Last

/-- The two translates of a hypothetical empty arc force incompatible root
gap and bridge lengths. All assumptions concern ordinary real sets. -/
theorem periodic_root_gap_contradiction {set : Set ℝ}
    {exponent period width gapLeft gapRight gapLength bridgeLength arcLeft : ℝ}
    (hperiod : 0 < period) (hwidth : 0 < width)
    (hgap : 0 < gapLength) (hbridge : 0 < bridgeLength)
    (hendpoint : -exponent * width ∈ set)
    (hgap_length : gapRight - gapLeft = exponent * gapLength)
    (hbridge_length : gapLeft + exponent * width = exponent * bridgeLength)
    (hgap_short : exponent * gapLength < period + width)
    (hproduct : gapLength * (period - width) < width * bridgeLength)
    (hroot : ∀ left : ℝ,
      -exponent * width ≤ left → left + width ≤ 0 →
      PeriodicSetAvoids set period left (left + width) →
      gapLeft ≤ left ∧ left + width ≤ gapRight)
    (hleft : -exponent * width ≤ arcLeft) (hright : arcLeft + width ≤ 0)
    (hempty : PeriodicSetAvoids set period arcLeft (arcLeft + width)) : False := by
  have hfirst := hroot arcLeft hleft hright hempty
  have htranslated : PeriodicSetAvoids set period
      (arcLeft - period) (arcLeft + width - period) := by
    intro point hpoint shift hinside
    apply hempty point hpoint (shift + 1)
    simp only [Int.cast_add, Int.cast_one, Set.mem_Ioo]
    constructor <;> nlinarith [hinside.1, hinside.2]
  have houtside : arcLeft + width - period ≤ -exponent * width := by
    by_contra hfailure
    have hsecond_right : -exponent * width < arcLeft + width - period := lt_of_not_ge hfailure
    have hsecond_left : -exponent * width ≤ arcLeft - period := by
      by_contra hleft_failure
      apply htranslated (-exponent * width) hendpoint 0
      simpa only [Int.cast_zero, zero_mul, add_zero, Set.mem_Ioo] using
        And.intro (lt_of_not_ge hleft_failure) hsecond_right
    have hsecond := hroot (arcLeft - period) hsecond_left
      (by linarith) (by convert htranslated using 1 <;> ring)
    linarith [hfirst.1, hfirst.2, hsecond.1, hsecond.2]
  have hscaled_gap : width ≤ exponent * gapLength := by
    linarith [hfirst.1, hfirst.2]
  have hscaled_bridge : exponent * bridgeLength ≤ period - width := by
    linarith [hfirst.1]
  have hgap_product := mul_le_mul_of_nonneg_right hscaled_gap hbridge.le
  have hbridge_product := mul_le_mul_of_nonneg_left hscaled_bridge hgap.le
  nlinarith

end LambdaCantor.Last
