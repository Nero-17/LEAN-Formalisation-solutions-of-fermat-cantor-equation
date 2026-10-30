import LambdaCantor.Last.EndpointTransferSource
import LambdaCantor.Last.EndpointTransferMargins
import LambdaCantor.Last.UniformCoefficient

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem endpoint_eventually_strict_corners {lower upper : ℝ} {lowerValues upperValues : ℕ → ℝ}
    (hlower : lower < 0) (hupper : 0 < upper)
    (hlowerLimit : Tendsto lowerValues atTop (𝓝 lower))
    (hupperLimit : Tendsto upperValues atTop (𝓝 upper)) :
    ∀ᶠ index in atTop, lowerValues index < 0 ∧ 0 < upperValues index :=
  (hlowerLimit.eventually (gt_mem_nhds hlower)).and (hupperLimit.eventually (lt_mem_nhds hupper))

theorem endpoint_normalizedCylinderSource_limit {exponent coefficient : ℝ}
    (hexponent : exponent ≠ 0) {scales coefficients : ℕ → ℝ}
    (hscales : ∀ index, 0 < scales index) (hscaleLimit : Tendsto scales atTop (𝓝 0))
    (hcoefficientLimit : Tendsto coefficients atTop (𝓝 coefficient))
    (firstLeft firstScale secondRight secondScale : ℝ) (point : ℝ × ℝ) :
    Tendsto (fun index => normalizedCylinderSource exponent (coefficients index) (scales index)
      firstLeft firstScale secondRight secondScale point) atTop
      (𝓝 ((firstLeft + firstScale * point.1) ^ exponent - coefficient * (secondRight - secondScale * point.2))) := by
  have hlimit := normalized_power_curve_limit hexponent hscales hscaleLimit hcoefficientLimit
    (firstLeft + firstScale * point.1) (secondRight - secondScale * point.2)
  convert hlimit using 1
  funext index
  unfold normalizedCylinderSource
  rw [show 1 - scales index * secondRight + scales index * secondScale * point.2 =
    1 - scales index * (secondRight - secondScale * point.2) by ring]
  field_simp [hexponent, (hscales index).ne']
  <;> ring

def EndpointRectangle.coefficient {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  exponent * ratio ^ ((source.secondOffset : ℝ) - source.firstOffset * exponent)

def EndpointRectangle.firstLowerDerivative {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  exponent * ratio ^ source.firstWord.length * (scalarWordMap ratio source.firstWord 0) ^ (exponent - 1)

def EndpointRectangle.firstUpperDerivative {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  exponent * ratio ^ source.firstWord.length * (scalarWordMap ratio source.firstWord 1) ^ (exponent - 1)

def EndpointRectangle.secondDerivative {exponent ratio : ℝ} (source : EndpointRectangle exponent ratio) : ℝ :=
  source.coefficient * ratio ^ source.secondWord.length

theorem endpoint_power_derivative_ratio_identity {exponent ratio base phase : ℝ}
    (hexponent : exponent ≠ 0) (hpositive : 0 < ratio) (hbase : 0 < base) (firstDepth secondDepth : ℕ) :
    (exponent * ratio ^ phase * ratio ^ secondDepth) /
      (exponent * ratio ^ firstDepth * base ^ (exponent - 1)) =
      ratio ^ (phase + (secondDepth : ℝ) - firstDepth) * base ^ (1 - exponent) := by
  conv_rhs =>
    rw [Real.rpow_sub hpositive, Real.rpow_add hpositive, Real.rpow_natCast, Real.rpow_natCast]
  rw [show 1 - exponent = -(exponent - 1) by ring, Real.rpow_neg hbase.le]
  field_simp [hexponent, (pow_pos hpositive firstDepth).ne',
    (Real.rpow_pos_of_pos hbase (exponent - 1)).ne']
  <;> ring

/-- The power endpoint model transfers to the actual Fermat curve for every
real exponent above one. All coefficient and derivative convergence is
constructed; no endpoint-to-actual transfer theorem is assumed. -/
theorem power_endpoint_to_actual {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (source : EndpointRectangle exponent ratio)
    (bands : TwoBandInterval ratio
      (source.secondDerivative / source.firstUpperDerivative)
      (source.secondDerivative / source.firstLowerDerivative)) :
    0 < dimH (intersection exponent ratio) := by
  have hless : ratio < 1 := by linarith
  have hexponent_positive : 0 < exponent := by linarith
  have hcoefficient : 0 < source.coefficient := by
    exact mul_pos hexponent_positive (Real.rpow_pos_of_pos hpositive _)
  have hfirst_scale : 0 < ratio ^ source.firstWord.length := pow_pos hpositive _
  have hsecond_scale : 0 < ratio ^ source.secondWord.length := pow_pos hpositive _
  have hfirst_left_bounds := scalarWordMap_bounds hpositive.le hless source.firstWord
    (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hfirst_right_bounds := scalarWordMap_bounds hpositive.le hless source.firstWord
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  have hfirst_endpoints : scalarWordMap ratio source.firstWord 0 ≤ scalarWordMap ratio source.firstWord 1 := by
    rw [scalarWordMap_affine ratio source.firstWord 1]
    nlinarith
  have hfirstLower : 0 < source.firstLowerDerivative := by
    exact mul_pos (mul_pos hexponent_positive hfirst_scale)
      (Real.rpow_pos_of_pos source.first_positive _)
  have hfirst_order : source.firstLowerDerivative ≤ source.firstUpperDerivative := by
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow source.first_positive.le hfirst_endpoints (by linarith))
      (mul_pos hexponent_positive hfirst_scale).le
  have hsecond : 0 < source.secondDerivative := mul_pos hcoefficient hsecond_scale
  obtain ⟨epsilon, hepsilon, hsecond_epsilon, hbands⟩ :=
    exists_two_band_vertical_margin hfirstLower hfirst_order hsecond bands
  obtain ⟨firstDepth, secondDepth, hfirstDepth, hsecondDepth, hscale_limit, hcoefficient_limit⟩ :=
    real_integer_endpoint_coefficient_sequences hexponent_positive hpositive hless
      source.firstOffset source.secondOffset
  have hcoefficient_limit' : Tendsto
      (fun index => exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
      atTop (𝓝 source.coefficient) := by
    simpa only [EndpointRectangle.coefficient, mul_comm exponent (source.firstOffset : ℝ)] using hcoefficient_limit
  have hvertical := coefficient_power_factor_eventually_uniform (exponent := exponent)
    (fun index => (pow_pos hpositive (secondDepth index)).le) hscale_limit hcoefficient_limit'
    (div_pos hepsilon hsecond_scale)
  have hlower_limit := endpoint_normalizedCylinderSource_limit hexponent_positive.ne'
    (fun index => pow_pos hpositive (secondDepth index)) hscale_limit hcoefficient_limit'
    (scalarWordMap ratio source.firstWord 0) (ratio ^ source.firstWord.length)
    (scalarWordMap ratio source.secondWord 1) (ratio ^ source.secondWord.length) (0, 0)
  have hupper_limit := endpoint_normalizedCylinderSource_limit hexponent_positive.ne'
    (fun index => pow_pos hpositive (secondDepth index)) hscale_limit hcoefficient_limit'
    (scalarWordMap ratio source.firstWord 0) (ratio ^ source.firstWord.length)
    (scalarWordMap ratio source.secondWord 1) (ratio ^ source.secondWord.length) (1, 1)
  have hfirst_endpoint : scalarWordMap ratio source.firstWord 0 + ratio ^ source.firstWord.length =
      scalarWordMap ratio source.firstWord 1 := by simpa using (scalarWordMap_affine ratio source.firstWord 1).symm
  have hsecond_endpoint : scalarWordMap ratio source.secondWord 1 - ratio ^ source.secondWord.length =
      scalarWordMap ratio source.secondWord 0 := by rw [scalarWordMap_affine ratio source.secondWord 1]; ring
  simp only [mul_zero, add_zero, sub_zero] at hlower_limit
  simp only [mul_one, hfirst_endpoint, hsecond_endpoint] at hupper_limit
  have hcorners := endpoint_eventually_strict_corners
    (sub_neg.mpr source.lower_corner) (sub_pos.mpr source.upper_corner) hlower_limit hupper_limit
  obtain ⟨index, hvertical_at, hcorners_at⟩ := (hvertical.and hcorners).exists
  apply positive_dimension_of_endpointAxisSource hpositive hless hexponent_positive
    (firstDepth index) (secondDepth index) source.firstWord source.secondWord
  apply two_band_positive_derivative_criterion
    (normalizedCylinderSource exponent
      (exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent)
      (ratio ^ secondDepth index) (scalarWordMap ratio source.firstWord 0)
      (ratio ^ source.firstWord.length) (scalarWordMap ratio source.secondWord 1)
      (ratio ^ source.secondWord.length))
    (fun point => exponent * ratio ^ source.firstWord.length *
      (scalarWordMap ratio source.firstWord 0 + ratio ^ source.firstWord.length * point.1) ^ (exponent - 1))
    (fun point => (exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent) *
      ratio ^ source.secondWord.length *
      (1 - ratio ^ secondDepth index * scalarWordMap ratio source.secondWord 1 +
        ratio ^ secondDepth index * ratio ^ source.secondWord.length * point.2) ^ (exponent - 1))
    (normalizedCylinderSource_continuous hexponent.le _ _ _ _ _ _)
    hpositive hhalf hfirstLower hfirst_order hbands
  · intro point hwidth hheight
    exact normalizedCylinderSource_hasStrictFDerivAt hexponent.le
      (pow_pos hpositive (secondDepth index)).ne' _ _ _ _ _ point
  · intro point hwidth hheight
    have hcoordinates := scalarWordMap_bounds hpositive.le hless source.firstWord hwidth
    have hleft : scalarWordMap ratio source.firstWord 0 ≤ scalarWordMap ratio source.firstWord point.1 := by
      rw [scalarWordMap_affine ratio source.firstWord point.1]
      nlinarith [hwidth.1]
    have hright : scalarWordMap ratio source.firstWord point.1 ≤ scalarWordMap ratio source.firstWord 1 := by
      rw [scalarWordMap_affine ratio source.firstWord point.1, scalarWordMap_affine ratio source.firstWord 1]
      nlinarith [hwidth.2]
    rw [← scalarWordMap_affine]
    exact ⟨mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow source.first_positive.le hleft (by linarith))
      (mul_pos hexponent_positive hfirst_scale).le,
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hcoordinates.1 hright (by linarith))
        (mul_pos hexponent_positive hfirst_scale).le⟩
  · intro point hwidth hheight
    have hreflected : 1 - point.2 ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hheight.1, hheight.2]
    have hcoordinates := scalarWordMap_bounds hpositive.le hless source.secondWord hreflected
    have hclose := hvertical_at (scalarWordMap ratio source.secondWord (1 - point.2)) hcoordinates
    have hbase : 1 - ratio ^ secondDepth index * scalarWordMap ratio source.secondWord 1 +
        ratio ^ secondDepth index * ratio ^ source.secondWord.length * point.2 =
        1 - ratio ^ secondDepth index * scalarWordMap ratio source.secondWord (1 - point.2) := by
      rw [scalarWordMap_affine ratio source.secondWord 1,
        scalarWordMap_affine ratio source.secondWord (1 - point.2)]
      ring
    rw [hbase]
    have hscaled := (mul_lt_mul_of_pos_left hclose hsecond_scale)
    have hcancel : ratio ^ source.secondWord.length *
        (epsilon / ratio ^ source.secondWord.length) = epsilon := by
      field_simp [hsecond_scale.ne']
    rw [hcancel] at hscaled
    have hidentity : ratio ^ source.secondWord.length *
        |(exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent) *
          (1 - ratio ^ secondDepth index * scalarWordMap ratio source.secondWord (1 - point.2)) ^ (exponent - 1) -
          source.coefficient| =
        |(exponent * ratio ^ secondDepth index / (ratio ^ firstDepth index) ^ exponent) *
          ratio ^ source.secondWord.length *
          (1 - ratio ^ secondDepth index * scalarWordMap ratio source.secondWord (1 - point.2)) ^ (exponent - 1) -
          source.secondDerivative| := by
      rw [← abs_of_pos hsecond_scale, ← abs_mul]
      congr 1
      unfold EndpointRectangle.secondDerivative
      rw [abs_of_pos hsecond_scale]
      ring
    rw [hidentity] at hscaled
    constructor <;> linarith [(abs_lt.mp hscaled).1, (abs_lt.mp hscaled).2]
  · exact ⟨hcorners_at.1, hcorners_at.2⟩

/-- Exact paper interface for the direct power orientation. -/
theorem power_endpoint_source_positive_dimension {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (source : EndpointRectangle exponent ratio)
    (bands : TwoBandInterval ratio source.powerLower source.powerUpper) :
    0 < dimH (intersection exponent ratio) := by
  have hless : ratio < 1 := by linarith
  have hright : 0 < scalarWordMap ratio source.firstWord 1 := by
    rw [scalarWordMap_affine ratio source.firstWord 1]
    nlinarith [source.first_positive, pow_pos hpositive source.firstWord.length]
  apply power_endpoint_to_actual hexponent hpositive hhalf source
  have hlower := endpoint_power_derivative_ratio_identity
    (show exponent ≠ 0 by linarith) hpositive hright source.firstWord.length source.secondWord.length
    (phase := (source.secondOffset : ℝ) - source.firstOffset * exponent)
  have hupper := endpoint_power_derivative_ratio_identity
    (show exponent ≠ 0 by linarith) hpositive source.first_positive source.firstWord.length source.secondWord.length
    (phase := (source.secondOffset : ℝ) - source.firstOffset * exponent)
  simpa only [EndpointRectangle.secondDerivative, EndpointRectangle.firstLowerDerivative,
    EndpointRectangle.firstUpperDerivative, EndpointRectangle.coefficient,
    hlower, hupper, EndpointRectangle.powerLower, EndpointRectangle.powerUpper] using bands

end LambdaCantor.Last
