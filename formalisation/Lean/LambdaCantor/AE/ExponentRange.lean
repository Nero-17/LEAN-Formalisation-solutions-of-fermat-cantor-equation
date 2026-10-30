import LambdaCantor.AE.ExponentWindow

noncomputable section
namespace LambdaCantor.AE

/-- The actual annular-energy restriction already places the Sobolev exponent
in the range needed for fractional mollifier cancellation. -/
theorem ae_regularity_lt_half {lower upper regularity : ℝ}
    (hlower : 0 < lower) (horder : lower ≤ upper) (hhalf : upper < 1 / 2)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    regularity < 1 / 2 := by
  have hgrowth := annulus_growth_gt_four hlower horder hhalf
  have hlog : 0 < Real.log (upper / lower ^ 3) :=
    Real.log_pos (by linarith)
  have hlog_order : Real.log (8 / 3 : ℝ) < Real.log (upper / lower ^ 3) :=
    Real.log_lt_log (by norm_num) (by linarith)
  have hquotient : 2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) < 2 :=
    (div_lt_iff₀ hlog).mpr (by linarith)
  linarith

theorem ae_regularity_le_one {lower upper regularity : ℝ}
    (hlower : 0 < lower) (horder : lower ≤ upper) (hhalf : upper < 1 / 2)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1) :
    regularity ≤ 1 := by
  have := ae_regularity_lt_half hlower horder hhalf hrange
  linarith

end LambdaCantor.AE
