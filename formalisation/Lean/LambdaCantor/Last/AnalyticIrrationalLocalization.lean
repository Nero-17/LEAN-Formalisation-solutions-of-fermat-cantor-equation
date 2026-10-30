import LambdaCantor.Last.AnalyticIrrationalGeometry
import LambdaCantor.Last.EndpointTransferLog

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem endpoint_scalar_cylinder_distance {ratio first second : ℝ} (hpositive : 0 < ratio)
    (word : List Bool) (hfirst : first ∈ Set.Icc (0 : ℝ) 1) (hsecond : second ∈ Set.Icc (0 : ℝ) 1) :
    |scalarWordMap ratio word first - scalarWordMap ratio word second| ≤ ratio ^ word.length := by
  rw [scalarWordMap_affine ratio word first, scalarWordMap_affine ratio word second,
    show scalarWordMap ratio word 0 + ratio ^ word.length * first -
      (scalarWordMap ratio word 0 + ratio ^ word.length * second) = ratio ^ word.length * (first - second) by ring,
    abs_mul, abs_of_pos (pow_pos hpositive _)]
  apply mul_le_of_le_one_right (pow_pos hpositive _).le
  exact abs_le.mpr ⟨by linarith [hfirst.1, hsecond.2], by linarith [hfirst.2, hsecond.1]⟩

/-- A strict logarithmic center admits positive cylinder hulls of the required
depth difference. The coefficient is chosen inside their open corner interval;
neither central Cantor point needs to avoid cylinder endpoints. -/
theorem localize_logarithmic_center {exponent ratio first second : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hfirst : 0 < first) (hsecond : 0 < second)
    (hfirst_mem : first ∈ cantorSet ratio) (hsecond_mem : second ∈ cantorSet ratio)
    (difference : ℕ)
    (hcenter : 1 < exponent * ratio ^ difference * second / first ∧
      1 / ratio - 1 - ratio < exponent * ratio ^ difference * second / first ∧
      exponent * ratio ^ difference * second / first < 1 / (1 - ratio)) :
    ∃ firstWord secondWord : List Bool, ∃ coefficient : ℝ, 0 < coefficient ∧
      0 < scalarWordMap ratio firstWord 0 ∧ 0 < scalarWordMap ratio secondWord 0 ∧
      (scalarWordMap ratio firstWord 0) ^ exponent < coefficient * scalarWordMap ratio secondWord 1 ∧
      coefficient * scalarWordMap ratio secondWord 0 < (scalarWordMap ratio firstWord 1) ^ exponent ∧
      TwoBandInterval ratio
        ((exponent * ratio ^ firstWord.length / scalarWordMap ratio firstWord 1) /
          (ratio ^ secondWord.length / scalarWordMap ratio secondWord 0))
        ((exponent * ratio ^ firstWord.length / scalarWordMap ratio firstWord 0) /
          (ratio ^ secondWord.length / scalarWordMap ratio secondWord 1)) := by
  have hless : ratio < 1 := by linarith
  have hcoefficient : 0 < exponent * ratio ^ difference := mul_pos (by linarith) (pow_pos hpositive _)
  have hcontinuous : ContinuousAt
      (fun pair : ℝ × ℝ => exponent * ratio ^ difference * pair.2 / pair.1) (first, second) :=
    (continuousAt_const.mul continuous_snd.continuousAt).div continuous_fst.continuousAt hfirst.ne'
  have hconditions : ∀ᶠ pair : ℝ × ℝ in 𝓝 (first, second),
      0 < pair.1 ∧ 0 < pair.2 ∧ 1 < exponent * ratio ^ difference * pair.2 / pair.1 ∧
      1 / ratio - 1 - ratio < exponent * ratio ^ difference * pair.2 / pair.1 ∧
      exponent * ratio ^ difference * pair.2 / pair.1 < 1 / (1 - ratio) :=
    (continuous_fst.continuousAt.eventually (lt_mem_nhds hfirst)).and
      ((continuous_snd.continuousAt.eventually (lt_mem_nhds hsecond)).and
      ((hcontinuous.eventually (lt_mem_nhds hcenter.1)).and
      ((hcontinuous.eventually (lt_mem_nhds hcenter.2.1)).and
       (hcontinuous.eventually (gt_mem_nhds hcenter.2.2)))))
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hconditions
  obtain ⟨start, hstart⟩ := exists_pow_lt_of_lt_one hradius hless
  obtain ⟨firstWord, hfirst_length, firstTail, hfirstTail, hfirst_eq⟩ :=
    exists_scalar_cylinder hpositive.le hless (start + difference) hfirst_mem
  obtain ⟨secondWord, hsecond_length, secondTail, hsecondTail, hsecond_eq⟩ :=
    exists_scalar_cylinder hpositive.le hless start hsecond_mem
  have hfirstTail_bounds := cantorSet_subset_unitInterval hpositive.le hless hfirstTail
  have hsecondTail_bounds := cantorSet_subset_unitInterval hpositive.le hless hsecondTail
  have hfirst_close : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      dist (scalarWordMap ratio firstWord coordinate) first < radius := by
    intro coordinate hcoordinate
    rw [hfirst_eq, Real.dist_eq]
    exact (endpoint_scalar_cylinder_distance hpositive firstWord hcoordinate hfirstTail_bounds).trans_lt
      ((pow_le_pow_of_le_one hpositive.le hless.le (by omega : start ≤ firstWord.length)).trans_lt hstart)
  have hsecond_close : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      dist (scalarWordMap ratio secondWord coordinate) second < radius := by
    intro coordinate hcoordinate
    rw [hsecond_eq, Real.dist_eq]
    exact (endpoint_scalar_cylinder_distance hpositive secondWord hcoordinate hsecondTail_bounds).trans_lt
      ((pow_le_pow_of_le_one hpositive.le hless.le (by omega : start ≤ secondWord.length)).trans_lt hstart)
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hconditions_lower := hball (show
      (scalarWordMap ratio firstWord 1, scalarWordMap ratio secondWord 0) ∈ Metric.ball (first, second) radius by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hfirst_close 1 hone, hsecond_close 0 hzero⟩)
  have hconditions_upper := hball (show
      (scalarWordMap ratio firstWord 0, scalarWordMap ratio secondWord 1) ∈ Metric.ball (first, second) radius by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hfirst_close 0 hzero, hsecond_close 1 hone⟩)
  have hfirstLeft := hconditions_upper.1
  have hfirstRight := hconditions_lower.1
  have hsecondLeft := hconditions_lower.2.1
  have hsecondRight := hconditions_upper.2.1
  have hfirst_order : scalarWordMap ratio firstWord 0 < scalarWordMap ratio firstWord 1 := by
    rw [scalarWordMap_affine ratio firstWord 1]
    nlinarith [pow_pos hpositive firstWord.length]
  have hsecond_order : scalarWordMap ratio secondWord 0 < scalarWordMap ratio secondWord 1 := by
    rw [scalarWordMap_affine ratio secondWord 1]
    nlinarith [pow_pos hpositive secondWord.length]
  have hcorner_interval : (scalarWordMap ratio firstWord 0) ^ exponent / scalarWordMap ratio secondWord 1 <
      (scalarWordMap ratio firstWord 1) ^ exponent / scalarWordMap ratio secondWord 0 := by
    apply (div_lt_div_of_pos_right
      (Real.rpow_lt_rpow hfirstLeft.le hfirst_order (by linarith)) hsecondRight).trans_le
    exact div_le_div₀ (Real.rpow_pos_of_pos hfirstRight exponent).le (le_refl _) hsecondLeft hsecond_order.le
  obtain ⟨coefficient, hcoefficient_interval⟩ := exists_between hcorner_interval
  have hcoefficient_positive : 0 < coefficient :=
    (div_pos (Real.rpow_pos_of_pos hfirstLeft exponent) hsecondRight).trans hcoefficient_interval.1
  have hdepth_difference : (firstWord.length : ℝ) - secondWord.length = difference := by
    rw [hfirst_length, hsecond_length, Nat.cast_add]
    ring
  have hband : TwoBandInterval ratio
      (exponent * ratio ^ difference * scalarWordMap ratio secondWord 0 / scalarWordMap ratio firstWord 1)
      (exponent * ratio ^ difference * scalarWordMap ratio secondWord 1 / scalarWordMap ratio firstWord 0) := by
    refine ⟨hconditions_lower.2.2.1, ?_, Or.inl ⟨hconditions_lower.2.2.2.1, hconditions_upper.2.2.2.2⟩⟩
    exact div_le_div₀ (mul_pos hcoefficient hsecondRight).le
      (mul_le_mul_of_nonneg_left hsecond_order.le hcoefficient.le) hfirstLeft hfirst_order.le
  refine ⟨firstWord, secondWord, coefficient, hcoefficient_positive, hfirstLeft, hsecondLeft,
    (div_lt_iff₀ hsecondRight).mp hcoefficient_interval.1,
    (lt_div_iff₀ hsecondLeft).mp hcoefficient_interval.2, ?_⟩
  rw [logarithmic_derivative_ratio_identity hpositive hfirstRight hsecondLeft,
    logarithmic_derivative_ratio_identity hpositive hfirstLeft hsecondRight,
    hdepth_difference, Real.rpow_natCast]
  exact hband

end LambdaCantor.Last
