import LambdaCantor.Last.AnalyticExceptionsQuadratic

noncomputable section
namespace LambdaCantor.Last

theorem rpow_half_square {base : ℝ} (hbase : 0 < base) :
    (base ^ (1 / 2 : ℝ)) ^ 2 = base := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
  norm_num

theorem rpow_three_halves_square {base : ℝ} (hbase : 0 < base) :
    (base ^ (3 / 2 : ℝ)) ^ 2 = base ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le]
  norm_num [Real.rpow_natCast]

theorem three_halves_derivative_ratio_square {ratio base : ℝ}
    (hpositive : 0 < ratio) (hbase : 0 < base) :
    (((3 / 2 : ℝ) * ratio ^ (1 / 2 : ℝ) * ratio ^ 2) /
      ((3 / 2 : ℝ) * ratio ^ 3 * base ^ (1 / 2 : ℝ))) ^ 2 = 1 / (ratio * base) := by
  rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
    rpow_half_square hpositive, rpow_half_square hbase]
  field_simp [hpositive.ne', hbase.ne']
  <;> ring

theorem second_band_of_inverse_product_squares {ratio lowerBase upperBase lowerSlope upperSlope : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerBase : 0 < lowerBase) (hbase_order : lowerBase ≤ upperBase)
    (hlowerSlope : 0 < lowerSlope) (hupperSlope : 0 < upperSlope)
    (hlower_square : lowerSlope ^ 2 = 1 / (ratio * upperBase))
    (hupper_square : upperSlope ^ 2 = 1 / (ratio * lowerBase))
    (habove_one : ratio * upperBase < 1)
    (hband_lower : (1 - ratio) ^ 2 * upperBase < ratio)
    (hband_upper : (1 - ratio - ratio ^ 2) ^ 2 < ratio * lowerBase) :
    TwoBandInterval ratio lowerSlope upperSlope := by
  have hupperBase : 0 < upperBase := hlowerBase.trans_le hbase_order
  have hdenominator : 0 < 1 - ratio - ratio ^ 2 := by nlinarith
  have hlow_square : 1 < lowerSlope ^ 2 := by
    rw [hlower_square, lt_div_iff₀ (mul_pos hpositive hupperBase)]
    simpa using habove_one
  have horder_square : lowerSlope ^ 2 ≤ upperSlope ^ 2 := by
    rw [hlower_square, hupper_square]
    exact one_div_le_one_div_of_le (mul_pos hpositive hlowerBase)
      (mul_le_mul_of_nonneg_left hbase_order hpositive.le)
  refine ⟨(sq_lt_sq₀ (show (0 : ℝ) ≤ 1 by norm_num) hlowerSlope.le).mp (by simpa using hlow_square),
    (sq_le_sq₀ hlowerSlope.le hupperSlope.le).mp horder_square, Or.inr ⟨?_, ?_⟩⟩
  · have hidentity : 1 / ratio - 1 = (1 - ratio) / ratio := by
      field_simp [hpositive.ne']
      <;> ring
    have hbound_square : ((1 - ratio) / ratio) ^ 2 < lowerSlope ^ 2 := by
      rw [div_pow, hlower_square, div_lt_div_iff₀ (sq_pos_of_pos hpositive) (mul_pos hpositive hupperBase)]
      nlinarith [mul_pos hpositive (sub_pos.mpr hband_lower)]
    rw [hidentity]
    exact (sq_lt_sq₀ (div_pos (show 0 < 1 - ratio by linarith) hpositive).le hlowerSlope.le).mp hbound_square
  · have hbound_square : upperSlope ^ 2 < (1 / (1 - ratio - ratio ^ 2)) ^ 2 := by
      rw [hupper_square, one_div_pow]
      exact one_div_lt_one_div_of_lt (sq_pos_of_pos hdenominator) hband_upper
    exact (sq_lt_sq₀ hupperSlope.le (one_div_pos.mpr hdenominator).le).mp hbound_square

theorem three_halves_endpoint_positive {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio < 1 / 2) :
    0 < dimH (intersection (3 / 2) ratio) := by
  have hpositive : 0 < ratio := by linarith
  have hfirst : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hpositive) (show 0 < 1 - ratio by linarith)]
  have hfirst_upper : 0 < 1 - ratio + ratio ^ 2 := by nlinarith [sq_nonneg ratio]
  have hsecond : 0 < 1 - ratio := by linarith
  have hfirstMap : scalarWordMap ratio [true, false, true] 0 =
      1 - ratio + ratio ^ 2 - ratio ^ 3 := by simp [scalarWordMap]; ring
  have hfirstUpperMap : scalarWordMap ratio [true, false, true] 1 =
      1 - ratio + ratio ^ 2 := by simp [scalarWordMap]; ring
  have hsecondMap : scalarWordMap ratio [true, false] 0 = 1 - ratio := by simp [scalarWordMap]
  have hsecondUpperMap : scalarWordMap ratio [true, false] 1 =
      1 - ratio + ratio ^ 2 := by simp [scalarWordMap]; ring
  have hcoefficient : 0 < (3 / 2 : ℝ) * ratio ^ (1 / 2 : ℝ) := by positivity
  have hcoefficient_square : ((3 / 2 : ℝ) * ratio ^ (1 / 2 : ℝ)) ^ 2 = (9 / 4 : ℝ) * ratio := by
    rw [mul_pow, rpow_half_square hpositive]
    norm_num
  have hlower_corner : (1 - ratio + ratio ^ 2 - ratio ^ 3) ^ (3 / 2 : ℝ) <
      (3 / 2 : ℝ) * ratio ^ (1 / 2 : ℝ) * (1 - ratio + ratio ^ 2) := by
    have hcertificate := three_halves_lower_corner_certificate hlower hupper.le
    apply (sq_lt_sq₀ (Real.rpow_pos_of_pos hfirst (3 / 2 : ℝ)).le
      (mul_pos hcoefficient hfirst_upper).le).mp
    rw [rpow_three_halves_square hfirst, mul_pow, hcoefficient_square]
    nlinarith
  have hupper_corner : (3 / 2 : ℝ) * ratio ^ (1 / 2 : ℝ) * (1 - ratio) <
      (1 - ratio + ratio ^ 2) ^ (3 / 2 : ℝ) := by
    have hcertificate := three_halves_upper_corner_certificate hlower hupper.le
    apply (sq_lt_sq₀ (mul_pos hcoefficient hsecond).le
      (Real.rpow_pos_of_pos hfirst_upper (3 / 2 : ℝ)).le).mp
    rw [mul_pow, hcoefficient_square, rpow_three_halves_square hfirst_upper]
    nlinarith
  let source : EndpointRectangle (3 / 2) ratio := {
    firstWord := [true, false, true]
    secondWord := [true, false]
    firstOffset := 1
    secondOffset := 2
    first_positive := by simpa only [hfirstMap] using hfirst
    second_positive := by simpa only [hsecondMap] using hsecond
    lower_corner := by
      convert hlower_corner using 1 <;> norm_num [hfirstMap, hsecondUpperMap]
    upper_corner := by
      convert hupper_corner using 1 <;> norm_num [hfirstUpperMap, hsecondMap] }
  apply power_endpoint_to_actual (by norm_num) hpositive hupper source
  apply second_band_of_inverse_product_squares hpositive hupper hfirst
    (show 1 - ratio + ratio ^ 2 - ratio ^ 3 ≤ 1 - ratio + ratio ^ 2 by nlinarith [pow_pos hpositive 3])
  · dsimp [source, EndpointRectangle.secondDerivative, EndpointRectangle.coefficient,
      EndpointRectangle.firstUpperDerivative]
    rw [hfirstUpperMap]
    positivity
  · dsimp [source, EndpointRectangle.secondDerivative, EndpointRectangle.coefficient,
      EndpointRectangle.firstLowerDerivative]
    rw [hfirstMap]
    positivity
  · convert three_halves_derivative_ratio_square hpositive hfirst_upper using 1 <;>
      norm_num [source, EndpointRectangle.secondDerivative, EndpointRectangle.coefficient,
        EndpointRectangle.firstUpperDerivative, hfirstUpperMap]
  · convert three_halves_derivative_ratio_square hpositive hfirst using 1 <;>
      norm_num [source, EndpointRectangle.secondDerivative, EndpointRectangle.coefficient,
        EndpointRectangle.firstLowerDerivative, hfirstMap]
  · have hbase_lt_one : 1 - ratio + ratio ^ 2 < 1 := by
      nlinarith [mul_pos hpositive (show 0 < 1 - ratio by linarith)]
    have hproduct := mul_lt_mul_of_pos_left hbase_lt_one hpositive
    nlinarith
  · nlinarith [three_halves_band_lower_certificate hlower hupper.le]
  · nlinarith [three_halves_band_upper_certificate hlower hupper.le]

theorem analytic_three_halves_last_strict_upper :
    lastTransition (3 / 2) < (Real.sqrt 3 - 1) / 2 := by
  have hbound : lastTransition (3 / 2) ≤ 4 / 11 := by
    apply lastTransition_le_of_nonnegative_bound (by norm_num)
    intro ratio hratio hlower
    rcases lt_or_eq_of_le hratio.2 with hhalf | hhalf
    · exact three_halves_endpoint_positive hlower.le hhalf
    · rw [hhalf]
      exact positive_dimH_intersection_half (by norm_num)
  apply hbound.trans_lt
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonnegative := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

end LambdaCantor.Last
