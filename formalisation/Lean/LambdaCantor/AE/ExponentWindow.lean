import LambdaCantor.AE.AnnulusSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

/-- The two limiting restrictions on twice the Sobolev exponent are compatible
above the actual threshold in the almost-everywhere dimension theorem. -/
theorem ae_exponent_compatibility {ratio : ℝ}
    (hthreshold : Real.sqrt 3 / 4 < ratio) (hhalf : ratio < 1 / 2) :
    0 < 1 - Real.log 2 / Real.log (1 / ratio) ∧
      1 - Real.log 2 / Real.log (1 / ratio) <
        Real.log (8 / 3 : ℝ) / Real.log (1 / ratio) - 1 := by
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have hratio : 0 < ratio := by nlinarith
  have hinverse : (2 : ℝ) < 1 / ratio := (lt_div_iff₀ hratio).mpr (by linarith)
  have hlog : 0 < Real.log (1 / ratio) := Real.log_pos (by linarith)
  have hlog_two : Real.log 2 < Real.log (1 / ratio) :=
    Real.log_lt_log (by norm_num) hinverse
  have hsquare : (3 / 16 : ℝ) < ratio ^ 2 := by nlinarith
  have hinverse_square : (1 / ratio) ^ 2 < (16 / 3 : ℝ) := by
    rw [div_pow]
    apply (div_lt_iff₀ (sq_pos_of_pos hratio)).mpr
    norm_num
    nlinarith
  have hlog_square := Real.log_lt_log (sq_pos_of_pos (by positivity : 0 < 1 / ratio))
    hinverse_square
  rw [Real.log_pow] at hlog_square
  have hlog_product : Real.log (16 / 3 : ℝ) = Real.log 2 + Real.log (8 / 3 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (8 / 3 : ℝ) ≠ 0)]
    norm_num
  rw [hlog_product] at hlog_square
  constructor
  · exact sub_pos.mpr ((div_lt_one hlog).mpr hlog_two)
  · apply (mul_lt_mul_iff_of_pos_right hlog).mp
    field_simp [hlog.ne'] <;> nlinarith

/-- At every parameter above the threshold, a positive regularity satisfies
all three strict numerical conditions at the diagonal interval. -/
theorem exists_ae_diagonal_exponent {ratio : ℝ}
    (hthreshold : Real.sqrt 3 / 4 < ratio) (hhalf : ratio < 1 / 2) :
    ∃ regularity : ℝ, 0 < regularity ∧ ratio ^ 2 / ratio < 1 ∧
      2 * regularity < 2 * Real.log (8 / 3 : ℝ) / Real.log (ratio / ratio ^ 3) - 1 ∧
      (ratio ^ 2 / ratio) ^ (2 * regularity) <
        ratio ^ (1 - Real.log 2 / Real.log (1 / ratio)) := by
  have hratio : 0 < ratio := lt_trans (by positivity) hthreshold
  have hless : ratio < 1 := by linarith
  obtain ⟨hlower_positive, hcompatible⟩ := ae_exponent_compatibility hthreshold hhalf
  obtain ⟨twiceRegularity, habove, hbelow⟩ := exists_between hcompatible
  have hlog : 0 < Real.log (1 / ratio) := Real.log_pos
    ((one_lt_div hratio).mpr hless)
  have hbase : ratio ^ 2 / ratio = ratio := by field_simp [hratio.ne'] <;> ring
  have hgrowth_log : Real.log (ratio / ratio ^ 3) = 2 * Real.log (1 / ratio) := by
    rw [Real.log_div hratio.ne' (pow_ne_zero _ hratio.ne'), Real.log_pow,
      Real.log_div one_ne_zero hratio.ne', Real.log_one]
    ring
  refine ⟨twiceRegularity / 2, by linarith, by simpa only [hbase] using hless, ?_, ?_⟩
  · rw [hgrowth_log]
    have hcancel : 2 * Real.log (8 / 3 : ℝ) / (2 * Real.log (1 / ratio)) =
        Real.log (8 / 3 : ℝ) / Real.log (1 / ratio) := by ring
    rw [hcancel]
    linarith
  · rw [hbase]
    apply Real.rpow_lt_rpow_of_exponent_gt hratio hless
    linarith

/-- Every parameter in the stated range lies in a genuine short interval
satisfying all numerical hypotheses of the freezing argument. -/
theorem exists_ae_exponent_window {ratio : ℝ}
    (hthreshold : Real.sqrt 3 / 4 < ratio) (hhalf : ratio < 1 / 2) :
    ∃ lower upper regularity : ℝ,
      Real.sqrt 3 / 4 < lower ∧ lower < ratio ∧ ratio < upper ∧ upper < 1 / 2 ∧
      0 < regularity ∧ upper ^ 2 / lower < 1 ∧
      2 * regularity < 2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1 ∧
      (upper ^ 2 / lower) ^ (2 * regularity) <
        upper ^ (1 - Real.log 2 / Real.log (1 / lower)) := by
  have hratio : 0 < ratio := lt_trans (by positivity) hthreshold
  obtain ⟨regularity, hregularity, hbase, hrange, hdecay⟩ :=
    exists_ae_diagonal_exponent hthreshold hhalf
  have hlower : ContinuousAt (fun offset : ℝ => ratio - offset) 0 := by fun_prop
  have hupper : ContinuousAt (fun offset : ℝ => ratio + offset) 0 := by fun_prop
  have hlower_ne : ratio - (0 : ℝ) ≠ 0 := by simpa using hratio.ne'
  have hupper_ne : ratio + (0 : ℝ) ≠ 0 := by simpa using hratio.ne'
  have hwidth := (hupper.pow 2).div hlower hlower_ne
  have hgrowth := hupper.div (hlower.pow 3) (pow_ne_zero _ hlower_ne)
  have hgrowth_ne : (ratio + (0 : ℝ)) / (ratio - 0) ^ 3 ≠ 0 :=
    div_ne_zero hupper_ne (pow_ne_zero _ hlower_ne)
  have hgrowth_log : Real.log ((ratio + (0 : ℝ)) / (ratio - 0) ^ 3) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    simpa using (lt_trans (by norm_num : (1 : ℝ) < 4)
      (annulus_growth_gt_four hratio le_rfl hhalf))
  have hlimit : ContinuousAt (fun offset : ℝ =>
      2 * Real.log (8 / 3 : ℝ) / Real.log ((ratio + offset) / (ratio - offset) ^ 3) - 1) 0 :=
    (continuousAt_const.div (hgrowth.log hgrowth_ne) hgrowth_log).sub continuousAt_const
  have hinverse := (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0).div
    hlower hlower_ne
  have hinverse_ne : (1 : ℝ) / (ratio - 0) ≠ 0 := div_ne_zero one_ne_zero hlower_ne
  have hinverse_log : Real.log ((1 : ℝ) / (ratio - 0)) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    simp only [sub_zero]
    exact (one_lt_div hratio).mpr (by linarith)
  have hdimension : ContinuousAt (fun offset : ℝ =>
      1 - Real.log 2 / Real.log (1 / (ratio - offset))) 0 :=
    continuousAt_const.sub (continuousAt_const.div (hinverse.log hinverse_ne) hinverse_log)
  have hleft := hwidth.rpow_const (Or.inr (show 0 ≤ 2 * regularity by positivity))
  have hright := hupper.rpow hdimension (Or.inl hupper_ne)
  have heventual : ∀ᶠ offset : ℝ in 𝓝 0,
      Real.sqrt 3 / 4 < ratio - offset ∧ ratio + offset < 1 / 2 ∧
      (ratio + offset) ^ 2 / (ratio - offset) < 1 ∧
      2 * regularity < 2 * Real.log (8 / 3 : ℝ) /
        Real.log ((ratio + offset) / (ratio - offset) ^ 3) - 1 ∧
      ((ratio + offset) ^ 2 / (ratio - offset)) ^ (2 * regularity) <
        (ratio + offset) ^ (1 - Real.log 2 / Real.log (1 / (ratio - offset))) := by
    filter_upwards [continuousAt_const.eventually_lt hlower (by simpa using hthreshold),
      hupper.eventually_lt continuousAt_const (by simpa using hhalf),
      hwidth.eventually_lt continuousAt_const (by simpa using hbase),
      continuousAt_const.eventually_lt hlimit (by simpa using hrange),
      hleft.eventually_lt hright (by simpa using hdecay)] with offset h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, by simpa only [one_div] using h₂, h₃, h₄, h₅⟩
  obtain ⟨radius, hradius, hball⟩ := Metric.eventually_nhds_iff.mp heventual
  have hinside : dist (radius / 2) (0 : ℝ) < radius := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  obtain ⟨hlower_threshold, hupper_half, hwidth_bound, hregularity_range, hdecay_bound⟩ :=
    hball hinside
  exact ⟨ratio - radius / 2, ratio + radius / 2, regularity,
    hlower_threshold, by linarith, by linarith, hupper_half, hregularity,
    hwidth_bound, hregularity_range, hdecay_bound⟩

end LambdaCantor.AE
