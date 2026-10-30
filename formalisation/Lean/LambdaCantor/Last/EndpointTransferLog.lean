import LambdaCantor.Last.EndpointTransferLogFunction

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- A logarithmic endpoint rectangle transfers along any actual depth
sequences with the correct limiting coefficient. The theorem covers both
all-real fixed endpoint phases and arbitrary irrational coefficients. -/
theorem logarithmic_endpoint_transfer_sequences {exponent ratio coefficient : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hcoefficient : 0 < coefficient) (firstWord secondWord : List Bool)
    (hfirst : 0 < scalarWordMap ratio firstWord 0)
    (hsecond : 0 < scalarWordMap ratio secondWord 0)
    (hlower_corner : (scalarWordMap ratio firstWord 0) ^ exponent <
      coefficient * scalarWordMap ratio secondWord 1)
    (hupper_corner : coefficient * scalarWordMap ratio secondWord 0 <
      (scalarWordMap ratio firstWord 1) ^ exponent)
    (bands : TwoBandInterval ratio
      ((exponent * ratio ^ firstWord.length / scalarWordMap ratio firstWord 1) /
        (ratio ^ secondWord.length / scalarWordMap ratio secondWord 0))
      ((exponent * ratio ^ firstWord.length / scalarWordMap ratio firstWord 0) /
        (ratio ^ secondWord.length / scalarWordMap ratio secondWord 1)))
    (firstDepth secondDepth : ℕ → ℕ)
    (hscale_limit : Tendsto (fun index => ratio ^ secondDepth index) atTop (𝓝 (0 : ℝ)))
    (hcoefficient_limit : Tendsto
      (fun index => exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
      atTop (𝓝 coefficient)) :
    0 < dimH (intersection exponent ratio) := by
  have hless : ratio < 1 := by linarith
  have hexponent_positive : 0 < exponent := by linarith
  let firstLeft := scalarWordMap ratio firstWord 0
  let firstRight := scalarWordMap ratio firstWord 1
  let secondLeft := scalarWordMap ratio secondWord 0
  let secondRight := scalarWordMap ratio secondWord 1
  let firstScale := ratio ^ firstWord.length
  let secondScale := ratio ^ secondWord.length
  have hfirstScale : 0 < firstScale := pow_pos hpositive _
  have hsecondScale : 0 < secondScale := pow_pos hpositive _
  have hfirstOrder : firstLeft ≤ firstRight := by
    dsimp [firstLeft, firstRight]
    rw [scalarWordMap_affine ratio firstWord 1]
    nlinarith
  have hsecondOrder : secondLeft ≤ secondRight := by
    dsimp [secondLeft, secondRight]
    rw [scalarWordMap_affine ratio secondWord 1]
    nlinarith
  have hfirstRight : 0 < firstRight := hfirst.trans_le hfirstOrder
  have hsecondRight : 0 < secondRight := hsecond.trans_le hsecondOrder
  have hsecondRight_unit := scalarWordMap_bounds hpositive.le hless secondWord
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hlowerS : 0 < secondScale / secondRight := div_pos hsecondScale hsecondRight
  have horderS : secondScale / secondRight ≤ secondScale / secondLeft :=
    div_le_div₀ hsecondScale.le (le_refl _) hsecond hsecondOrder
  have horderT : exponent * firstScale / firstRight ≤ exponent * firstScale / firstLeft :=
    div_le_div₀ (mul_pos hexponent_positive hfirstScale).le (le_refl _) hfirst hfirstOrder
  obtain ⟨epsilon, hepsilon, hlowerS_epsilon, hbands⟩ :=
    exists_two_band_horizontal_margin hlowerS horderS horderT bands
  let firstCutoff := firstLeft / 2
  let dropCutoff := coefficient * secondLeft / 4
  have hfirstCutoff : 0 < firstCutoff := by dsimp [firstCutoff]; positivity
  have hdropCutoff : 0 < dropCutoff := by dsimp [dropCutoff]; positivity
  have hdrop_limit := normalizedPowerDrop_limit hexponent_positive.ne'
    (fun index => pow_pos hpositive (secondDepth index)) hscale_limit hcoefficient_limit secondLeft
  have hdrop_eventual : ∀ᶠ index in atTop,
      coefficient * secondLeft / 2 < normalizedPowerDrop exponent
        (exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
        (ratio ^ secondDepth index) secondLeft :=
    hdrop_limit.eventually (lt_mem_nhds (by nlinarith [mul_pos hcoefficient hsecond]))
  have hlog_uniform := power_log_derivative_eventually_uniform hexponent_positive hsecond
    (fun index => pow_pos hpositive (secondDepth index)) hscale_limit (div_pos hepsilon hsecondScale)
  have hscale_small : ∀ᶠ index in atTop, ratio ^ secondDepth index < 1 :=
    hscale_limit.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlog_lower_limit : Tendsto
      (fun index => logarithmicCylinderSource exponent
        (exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
        (ratio ^ secondDepth index) firstLeft firstScale secondRight secondScale firstCutoff dropCutoff (0, 0))
      atTop (𝓝 (exponent * Real.log firstLeft - Real.log (coefficient * secondRight))) := by
    have hdrop_right := normalizedPowerDrop_limit hexponent_positive.ne'
      (fun index => pow_pos hpositive (secondDepth index)) hscale_limit hcoefficient_limit secondRight
    have hlimit := (tendsto_const_nhds (x := exponent * cutoffLog firstCutoff firstLeft)).sub
      ((cutoffLog_continuous hdropCutoff).continuousAt.tendsto.comp hdrop_right)
    simpa only [logarithmicCylinderSource, Function.comp_apply, mul_zero, add_zero, sub_zero,
      cutoffLog_eq (show firstCutoff ≤ firstLeft by dsimp [firstCutoff]; linarith only [hfirst]),
      cutoffLog_eq (show dropCutoff ≤ coefficient * secondRight by
        dsimp [dropCutoff]; nlinarith only [mul_pos hcoefficient hsecond,
          mul_le_mul_of_nonneg_left hsecondOrder hcoefficient.le])] using hlimit
  have hlog_upper_limit : Tendsto
      (fun index => logarithmicCylinderSource exponent
        (exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
        (ratio ^ secondDepth index) firstLeft firstScale secondRight secondScale firstCutoff dropCutoff (1, 1))
      atTop (𝓝 (exponent * Real.log firstRight - Real.log (coefficient * secondLeft))) := by
    have hfirst_endpoint : firstLeft + firstScale = firstRight := by
      simpa only [firstLeft, firstScale, firstRight, mul_one] using (scalarWordMap_affine ratio firstWord 1).symm
    have hsecond_endpoint : secondRight - secondScale = secondLeft := by
      dsimp [secondLeft, secondRight, secondScale]
      rw [scalarWordMap_affine ratio secondWord 1]
      ring
    have hlimit := (tendsto_const_nhds (x := exponent * cutoffLog firstCutoff firstRight)).sub
      ((cutoffLog_continuous hdropCutoff).continuousAt.tendsto.comp hdrop_limit)
    simpa only [logarithmicCylinderSource, Function.comp_apply, mul_one, hfirst_endpoint, hsecond_endpoint,
      cutoffLog_eq (show firstCutoff ≤ firstRight by dsimp [firstCutoff]; linarith only [hfirst, hfirstOrder]),
      cutoffLog_eq (show dropCutoff ≤ coefficient * secondLeft by
        dsimp [dropCutoff]; linarith only [mul_pos hcoefficient hsecond])] using hlimit
  have hlower_negative : exponent * Real.log firstLeft - Real.log (coefficient * secondRight) < 0 := by
    have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hfirst exponent) hlower_corner
    rw [Real.log_rpow hfirst] at hlog
    linarith
  have hupper_positive : 0 < exponent * Real.log firstRight - Real.log (coefficient * secondLeft) := by
    have hlog := Real.log_lt_log (mul_pos hcoefficient hsecond) hupper_corner
    rw [Real.log_rpow hfirstRight] at hlog
    linarith
  have hcorners := endpoint_eventually_strict_corners hlower_negative hupper_positive hlog_lower_limit hlog_upper_limit
  obtain ⟨index, hdrop_at, hlog_at, hscale_at, hcorners_at⟩ :=
    (hdrop_eventual.and (hlog_uniform.and (hscale_small.and hcorners))).exists
  have hactual_coefficient : 0 < exponent * ratio ^ secondDepth index /
      (ratio ^ firstDepth index) ^ exponent := by positivity
  have hfirst_bounds : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      firstLeft ≤ firstLeft + firstScale * coordinate ∧
        firstLeft + firstScale * coordinate ≤ firstRight := by
    intro coordinate hcoordinate
    have hendpoint : firstLeft + firstScale = firstRight := by
      simpa only [firstLeft, firstScale, firstRight, mul_one] using (scalarWordMap_affine ratio firstWord 1).symm
    constructor <;> nlinarith [hcoordinate.1, hcoordinate.2]
  have hsecond_bounds : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      secondRight - secondScale * coordinate ∈ Set.Icc secondLeft 1 := by
    intro coordinate hcoordinate
    have hendpoint : secondRight - secondScale = secondLeft := by
      dsimp [secondRight, secondScale, secondLeft]
      rw [scalarWordMap_affine ratio secondWord 1]
      ring
    constructor <;> nlinarith [hcoordinate.1, hcoordinate.2, hsecondRight_unit.2]
  have hdrop_bounds : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      dropCutoff < normalizedPowerDrop exponent
        (exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
        (ratio ^ secondDepth index) (secondRight - secondScale * coordinate) := by
    intro coordinate hcoordinate
    have hbounds := hsecond_bounds coordinate hcoordinate
    have hmonotone := normalizedPowerDrop_mono_on_unit hexponent_positive hactual_coefficient.le
      (pow_pos hpositive (secondDepth index)) hscale_at
      (show secondLeft ∈ Set.Icc (0 : ℝ) 1 from ⟨hsecond.le, hsecondOrder.trans hsecondRight_unit.2⟩)
      (show secondRight - secondScale * coordinate ∈ Set.Icc (0 : ℝ) 1 from
        ⟨hsecond.le.trans hbounds.1, hbounds.2⟩) hbounds.1
    dsimp [dropCutoff]
    nlinarith [mul_pos hcoefficient hsecond]
  have hdimension : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      logarithmicCylinderSource exponent
        (exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
        (ratio ^ secondDepth index) firstLeft firstScale secondRight secondScale firstCutoff dropCutoff point = 0} := by
    apply two_band_positive_derivative_criterion _
      (fun point => secondScale * powerLogDerivative exponent (ratio ^ secondDepth index)
        (secondRight - secondScale * point.1))
      (fun point => exponent * firstScale / (firstLeft + firstScale * point.2))
      (logarithmicCylinderSource_continuous hexponent.le hfirstCutoff hdropCutoff _ _ _ _ _ _)
      hpositive hhalf hlowerS_epsilon (by linarith only [horderS, hepsilon]) hbands
    · intro point hwidth hheight
      apply logarithmicCylinderSource_powerLogDerivative hexponent.le (pow_pos hpositive (secondDepth index)).ne'
        hfirstCutoff hdropCutoff _ _ _ _ _ hactual_coefficient.ne' point
      · have hbounds := hfirst_bounds point.2 hheight
        dsimp [firstCutoff]
        linarith
      · exact hdrop_bounds point.1 hwidth
    · intro point hwidth hheight
      have hbounds := hsecond_bounds point.1 hwidth
      have hclose := (hlog_at (secondRight - secondScale * point.1) hbounds).2
      have hscaled := mul_lt_mul_of_pos_left hclose hsecondScale
      have hcancel : secondScale * (epsilon / secondScale) = epsilon := by field_simp [hsecondScale.ne']
      rw [hcancel] at hscaled
      have herror : |secondScale * powerLogDerivative exponent (ratio ^ secondDepth index)
          (secondRight - secondScale * point.1) - secondScale / (secondRight - secondScale * point.1)| < epsilon := by
        rw [div_eq_mul_one_div, ← mul_sub, abs_mul, abs_of_pos hsecondScale]
        exact hscaled
      have hcoordinate_positive : 0 < secondRight - secondScale * point.1 := hsecond.trans_le hbounds.1
      have hbase_lower : secondScale / secondRight ≤ secondScale / (secondRight - secondScale * point.1) :=
        div_le_div₀ hsecondScale.le (le_refl _) hcoordinate_positive
          (sub_le_self _ (mul_nonneg hsecondScale.le hwidth.1))
      have hbase_upper : secondScale / (secondRight - secondScale * point.1) ≤ secondScale / secondLeft :=
        div_le_div₀ hsecondScale.le (le_refl _) hsecond hbounds.1
      constructor <;> linarith only [hbase_lower, hbase_upper, (abs_lt.mp herror).1, (abs_lt.mp herror).2]
    · intro point hwidth hheight
      have hbounds := hfirst_bounds point.2 hheight
      have hcoordinate_positive : 0 < firstLeft + firstScale * point.2 := hfirst.trans_le hbounds.1
      exact ⟨div_le_div₀ (mul_pos hexponent_positive hfirstScale).le (le_refl _) hcoordinate_positive hbounds.2,
        div_le_div₀ (mul_pos hexponent_positive hfirstScale).le (le_refl _) hfirst hbounds.1⟩
    · exact ⟨hcorners_at.1, hcorners_at.2⟩
  have hswap : Isometry (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    apply Isometry.of_dist_eq
    intro first second
    simp only [Prod.dist_eq, Prod.fst_swap, Prod.snd_swap, max_comm]
  apply positive_dimension_of_endpointAxisSource hpositive hless hexponent_positive
    (firstDepth index) (secondDepth index) firstWord secondWord
  apply hdimension.trans_le ((hswap.antilipschitz.le_dimH_image _).trans (dimH_mono ?_))
  rintro point ⟨value, hvalue, rfl⟩
  have hwidth := cantorSet_subset_unitInterval hpositive.le hless hvalue.1.1
  have hheight := cantorSet_subset_unitInterval hpositive.le hless hvalue.1.2
  refine ⟨⟨hvalue.1.2, hvalue.1.1⟩, ?_⟩
  apply logarithmicCylinderSource_zero_power_equation hexponent_positive
    (pow_pos hpositive (secondDepth index)).ne' hfirstCutoff hdropCutoff value _
    (hdrop_bounds value.1 hwidth).le hvalue.2
  have hbounds := hfirst_bounds value.2 hheight
  dsimp [firstCutoff]
  linarith

theorem logarithmic_derivative_ratio_identity {exponent ratio first second : ℝ}
    (hpositive : 0 < ratio) (hfirst : 0 < first) (hsecond : 0 < second)
    (firstDepth secondDepth : ℕ) :
    (exponent * ratio ^ firstDepth / first) / (ratio ^ secondDepth / second) =
      exponent * ratio ^ ((firstDepth : ℝ) - secondDepth) * second / first := by
  rw [Real.rpow_sub hpositive, Real.rpow_natCast, Real.rpow_natCast]
  field_simp [hfirst.ne', hsecond.ne', (pow_pos hpositive secondDepth).ne']
  <;> ring

/-- Exact paper interface for a logarithmic endpoint rectangle. -/
theorem logarithmic_endpoint_source_positive_dimension {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (source : EndpointRectangle exponent ratio)
    (bands : TwoBandInterval ratio source.logLower source.logUpper) :
    0 < dimH (intersection exponent ratio) := by
  have hexponent_positive : 0 < exponent := by linarith
  have hless : ratio < 1 := by linarith
  have hcoefficient : 0 < source.coefficient :=
    mul_pos hexponent_positive (Real.rpow_pos_of_pos hpositive _)
  have hfirstRight : 0 < scalarWordMap ratio source.firstWord 1 := by
    rw [scalarWordMap_affine ratio source.firstWord 1]
    nlinarith [source.first_positive, pow_pos hpositive source.firstWord.length]
  have hsecondRight : 0 < scalarWordMap ratio source.secondWord 1 := by
    rw [scalarWordMap_affine ratio source.secondWord 1]
    nlinarith [source.second_positive, pow_pos hpositive source.secondWord.length]
  obtain ⟨firstDepth, secondDepth, hfirstDepth, hsecondDepth, hscale_limit, hcoefficient_limit⟩ :=
    real_integer_endpoint_coefficient_sequences hexponent_positive hpositive hless
      source.firstOffset source.secondOffset
  refine logarithmic_endpoint_transfer_sequences hexponent hpositive hhalf hcoefficient
    source.firstWord source.secondWord source.first_positive source.second_positive
    source.lower_corner source.upper_corner ?_ firstDepth secondDepth hscale_limit ?_
  · have hlower := logarithmic_derivative_ratio_identity (exponent := exponent) hpositive
      hfirstRight source.second_positive source.firstWord.length source.secondWord.length
    have hupper := logarithmic_derivative_ratio_identity (exponent := exponent) hpositive
      source.first_positive hsecondRight source.firstWord.length source.secondWord.length
    simpa only [hlower, hupper, EndpointRectangle.logLower, EndpointRectangle.logUpper] using bands
  · simpa only [EndpointRectangle.coefficient, mul_comm exponent (source.firstOffset : ℝ)] using hcoefficient_limit

end LambdaCantor.Last
