import LambdaCantor.First.Dimension

noncomputable section
namespace LambdaCantor.First

theorem projection_cost_lt_one {ratio projectionExponent targetExponent : ℝ}
    (hratio : 0 < ratio) (hcontract : ratio < 1)
    (hexponents : Real.log 4 / Real.log (1 / ratio) < projectionExponent + targetExponent) :
    4 * ratio ^ (projectionExponent + targetExponent) < 1 := by
  have hlog := log_reciprocal_pos hratio hcontract
  have hproduct := (div_lt_iff₀ hlog).1 hexponents
  have hlogRatio : Real.log ratio = -Real.log (1 / ratio) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hratio), Real.log_one]
    ring
  apply (Real.log_lt_log_iff
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos hratio _)) zero_lt_one).1
  rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hratio _)),
    Real.log_rpow hratio, Real.log_one, hlogRatio]
  nlinarith

/-- Any target exponent above the printed dimension bound admits a projection
exponent allowed by Shmerkin's theorem and giving a strictly decaying cost. -/
theorem exists_projection_exponent {ratio targetExponent : ℝ}
    (hratio : 0 < ratio) (hcontract : ratio < 1)
    (htarget : dimensionUpperBound ratio < targetExponent) :
    ∃ projectionExponent : ℝ, 0 < projectionExponent ∧
      projectionExponent < min (Real.log 4 / Real.log (1 / ratio)) 1 ∧
      4 * ratio ^ (projectionExponent + targetExponent) < 1 := by
  have hpositiveTarget : 0 < targetExponent :=
    (dimensionUpperBound_nonneg ratio).trans_lt htarget
  have hpositiveDimension : 0 < Real.log 4 / Real.log (1 / ratio) :=
    div_pos (Real.log_pos (by norm_num)) (log_reciprocal_pos hratio hcontract)
  have hdimension : Real.log 4 / Real.log (1 / ratio) - 1 < targetExponent := by
    rw [log_four]
    exact (le_max_left _ _).trans_lt htarget
  have hinterval : max 0 (Real.log 4 / Real.log (1 / ratio) - targetExponent) <
      min (Real.log 4 / Real.log (1 / ratio)) 1 := by
    apply lt_min
    · exact max_lt hpositiveDimension (by linarith)
    · exact max_lt zero_lt_one (by linarith)
  obtain ⟨projectionExponent, hlower, hupper⟩ := exists_between hinterval
  refine ⟨projectionExponent, (le_max_left _ _).trans_lt hlower, hupper, ?_⟩
  apply projection_cost_lt_one hratio hcontract
  have h := (le_max_right 0
    (Real.log 4 / Real.log (1 / ratio) - targetExponent)).trans_lt hlower
  linarith

end LambdaCantor.First
