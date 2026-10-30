import LambdaCantor.Last.TwoBandSlopes
import LambdaCantor.Last.TwoBandOuterQuotient

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- A slightly stronger rational parameter threshold is available for the
trimmed first-band construction. It lies strictly below the paper's c. -/
theorem rational_trimmed_first_band {ratio slope : ℝ}
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hhalf : ratio < 1 / 2)
    (hslower : (7 / 5 : ℝ) < slope) (hsupper : slope < 31 / 20) :
    1 < slope ∧ 1 / ratio - 1 - ratio < slope ∧ slope < 1 / (1 - ratio) := by
  have hpositive : 0 < ratio := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · have hsquare : (183 / 500 : ℝ) ^ 2 ≤ ratio ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlower) (show 0 ≤ ratio + 183 / 500 by linarith)]
    have hbound := mul_pos hpositive (sub_pos.mpr hslower)
    have hgoal : 1 < ratio * (slope + 1 + ratio) := by nlinarith
    have hdivision : 1 / ratio < slope + 1 + ratio :=
      (div_lt_iff₀ hpositive).mpr (by simpa only [mul_comm] using hgoal)
    linarith
  · rw [lt_div_iff₀ (show 0 < 1 - ratio by linarith)]
    nlinarith [mul_pos (sub_pos.mpr hsupper) (show 0 < 1 - ratio by linarith)]

theorem rational_trimmed_band {ratio slope : ℝ}
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hhalf : ratio < 1 / 2)
    (hslower : (7 / 5 : ℝ) < slope) (hsupper : slope < 31 / 20) :
    TwoBandSlopes ratio slope := by
  have hband := rational_trimmed_first_band hlower hhalf hslower hsupper
  exact ⟨hband.1, Or.inl hband.2⟩

theorem phase_power_enters_open_interval {ratio exponent lower upper : ℝ}
    (hpositive : 0 < ratio) (hless : ratio < 1) (hexponent : 0 < exponent)
    (hlower : lower < exponent) (hupper : 0 < upper) (hwidth : lower < ratio * upper) :
    ∃ depth : ℕ, exponent * ratio ^ depth ∈ Set.Ioo lower upper := by
  have hlimit : Tendsto (fun depth : ℕ => exponent * ratio ^ depth) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless)
  have hexists : ∃ depth : ℕ, exponent * ratio ^ depth < upper :=
    (hlimit.eventually (gt_mem_nhds hupper)).exists
  refine ⟨Nat.find hexists, ?_, Nat.find_spec hexists⟩
  cases hdepth : Nat.find hexists with
  | zero => simpa [hdepth] using hlower
  | succ previous =>
      have hprevious : upper ≤ exponent * ratio ^ previous :=
        le_of_not_gt (Nat.find_min hexists (by omega))
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hprevious hpositive.le]

/-- Geometric outer-quotient source for every exponent above one.
Irrationality is needed only for the later coefficient approximation. -/
theorem exists_trimmed_logarithmic_center {ratio exponent : ℝ}
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hhalf : ratio < 1 / 2) (hexponent : 1 < exponent) :
    ∃ depth : ℕ, ∃ first ∈ outerCantor ratio, ∃ second ∈ outerCantor ratio,
      (7 / 5 : ℝ) < exponent * ratio ^ depth * second / first ∧
      exponent * ratio ^ depth * second / first < 31 / 20 := by
  have hpositive : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hcomplement : 0 < 1 - ratio := by linarith
  have hwidth_polynomial : 28 * (1 - ratio) ^ 2 < 31 * ratio := by
    have hcertificate := mul_nonneg (sub_nonneg.mpr hlower)
      (show 0 ≤ 87 - 28 * (ratio + 183 / 500) by linarith)
    nlinarith
  have hwidth : (7 / 5 : ℝ) * (1 - ratio) < ratio * ((31 / 20 : ℝ) / (1 - ratio)) := by
    rw [← mul_div_assoc, lt_div_iff₀ hcomplement]
    nlinarith [hwidth_polynomial]
  obtain ⟨depth, hphase⟩ := phase_power_enters_open_interval hpositive hless
    (show 0 < exponent by linarith) (show (7 / 5 : ℝ) * (1 - ratio) < exponent by linarith)
    (div_pos (by norm_num) hcomplement) hwidth
  let phase := exponent * ratio ^ depth
  have hphase_positive : 0 < phase := mul_pos (by linarith) (pow_pos hpositive _)
  have hinterval : max (7 / 5 : ℝ) (phase * (1 - ratio)) <
      min (31 / 20 : ℝ) (phase / (1 - ratio)) := by
    apply max_lt
    · apply lt_min (by norm_num)
      exact (lt_div_iff₀ hcomplement).mpr hphase.1
    · apply lt_min
      · exact (lt_div_iff₀ hcomplement).mp hphase.2
      · rw [lt_div_iff₀ hcomplement]
        nlinarith [mul_pos hphase_positive (show 0 < 1 - (1 - ratio) ^ 2 by nlinarith)]
  obtain ⟨slope, hslope⟩ := exists_between hinterval
  have hslower : (7 / 5 : ℝ) < slope := (le_max_left _ _).trans_lt hslope.1
  have hsupper : slope < (31 / 20 : ℝ) := hslope.2.trans_le (min_le_left _ _)
  have hslope_positive : 0 < slope := by linarith
  have hquotient : phase / slope ∈ outerQuotients ratio := by
    rw [two_band_outerQuotients_eq_interval (by linarith) hhalf]
    constructor
    · rw [le_div_iff₀ hslope_positive]
      have hupper := hslope.2.trans_le (min_le_right _ _)
      have hbound := (lt_div_iff₀ hcomplement).mp hupper
      nlinarith
    · rw [inv_eq_one_div, div_le_div_iff₀ hslope_positive hcomplement]
      simpa only [one_mul] using (le_max_right (7 / 5 : ℝ) (phase * (1 - ratio))).trans hslope.1.le
  obtain ⟨first, hfirst, second, hsecond, hquotient_eq⟩ := hquotient
  have hfirst_positive : 0 < first := by
    have hbound := outerCantor_bounds hpositive.le hless hfirst
    linarith [hbound.1]
  have hsecond_positive : 0 < second := by
    have hbound := outerCantor_bounds hpositive.le hless hsecond
    linarith [hbound.1]
  have hidentity : exponent * ratio ^ depth * second / first = slope := by
    have hratio_eq := (div_eq_div_iff hslope_positive.ne' hsecond_positive.ne').mp hquotient_eq
    apply (div_eq_iff hfirst_positive.ne').mpr
    dsimp [phase] at hratio_eq
    nlinarith
  exact ⟨depth, first, hfirst, second, hsecond,
    by simpa only [hidentity] using hslower, by simpa only [hidentity] using hsupper⟩

end LambdaCantor.Last
