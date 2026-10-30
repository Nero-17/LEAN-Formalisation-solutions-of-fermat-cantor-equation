import LambdaCantor.Last.AnalyticExceptionsGeometry
import LambdaCantor.Last.EndpointTransferPower
import LambdaCantor.Last.AnalyticLastPersistence
import LambdaCantor.Half

noncomputable section
namespace LambdaCantor.Last

theorem cubic_low_endpoint_positive {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ 3 / 8) :
    0 < dimH (intersection 3 ratio) := by
  have hpositive : 0 < ratio := by linarith
  have hhalf : ratio < 1 / 2 := by linarith
  have hgeometry := cubic_low_source_geometry hlower hupper
  dsimp only at hgeometry
  have hfirst : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hpositive) (show 0 < 1 - ratio by linarith)]
  have hfirst_upper : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 + ratio ^ 4 := by positivity
  have hcomplement_square : 1 - ratio * 2 + ratio ^ 2 ≠ 0 := by
    convert (sq_pos_of_pos (show 0 < 1 - ratio by linarith)).ne' using 1 <;> ring
  have hfirst_upper_square :
      1 - ratio * 2 + ratio ^ 2 * 3 - ratio ^ 3 * 4 + ratio ^ 4 * 5 -
        ratio ^ 5 * 4 + ratio ^ 6 * 3 - ratio ^ 7 * 2 + ratio ^ 8 ≠ 0 := by
    convert (sq_pos_of_pos hfirst_upper).ne' using 1 <;> ring
  let source : EndpointRectangle 3 ratio := {
    firstWord := [true, false, true, false]
    secondWord := [true, true]
    firstOffset := 0
    secondOffset := 2
    first_positive := by dsimp [scalarWordMap]; nlinarith [hfirst]
    second_positive := by simp [scalarWordMap]; nlinarith [sq_nonneg ratio]
    lower_corner := by
      norm_num [scalarWordMap, Real.rpow_natCast]
      nlinarith [hgeometry.2.1]
    upper_corner := by
      norm_num [scalarWordMap, Real.rpow_natCast]
      nlinarith [hgeometry.2.2] }
  apply power_endpoint_to_actual (by norm_num) hpositive hhalf source
  convert hgeometry.1 using 1 <;>
    dsimp [source, EndpointRectangle.secondDerivative, EndpointRectangle.coefficient,
      EndpointRectangle.firstLowerDerivative, EndpointRectangle.firstUpperDerivative] <;>
    norm_num [scalarWordMap, Real.rpow_natCast] <;>
    field_simp [hpositive.ne', hfirst.ne', hfirst_upper.ne'] <;>
    ring_nf <;> field_simp [hcomplement_square, hfirst_upper_square] <;> ring

theorem cubic_high_endpoint_positive {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio < 1 / 2) :
    0 < dimH (intersection 3 ratio) := by
  have hpositive : 0 < ratio := by linarith
  have hgeometry := cubic_high_source_geometry hlower hupper
  dsimp only at hgeometry
  have hfirst : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hpositive) (show 0 < 1 - ratio by linarith)]
  have hfirst_upper : 0 < 1 - ratio + ratio ^ 2 := by nlinarith [sq_nonneg ratio]
  have hcomplement_square : 1 - ratio * 2 + ratio ^ 2 ≠ 0 := by
    convert (sq_pos_of_pos (show 0 < 1 - ratio by linarith)).ne' using 1 <;> ring
  let source : EndpointRectangle 3 ratio := {
    firstWord := [true, false, true]
    secondWord := [true]
    firstOffset := 0
    secondOffset := 2
    first_positive := by dsimp [scalarWordMap]; nlinarith [hfirst]
    second_positive := by simp [scalarWordMap]; linarith
    lower_corner := by
      norm_num [scalarWordMap, Real.rpow_natCast]
      nlinarith [hgeometry.2.1]
    upper_corner := by
      norm_num [scalarWordMap, Real.rpow_natCast]
      nlinarith [hgeometry.2.2] }
  apply power_endpoint_to_actual (by norm_num) hpositive hupper source
  convert hgeometry.1 using 1 <;>
    dsimp [source, EndpointRectangle.secondDerivative, EndpointRectangle.coefficient,
      EndpointRectangle.firstLowerDerivative, EndpointRectangle.firstUpperDerivative] <;>
    norm_num [scalarWordMap, Real.rpow_natCast] <;>
    field_simp [hpositive.ne', hfirst.ne', hfirst_upper.ne'] <;>
    ring_nf <;> field_simp [hcomplement_square] <;> ring

theorem analytic_cubic_positive_dimension {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio < 1 / 2) :
    0 < dimH (intersection 3 ratio) := by
  by_cases hsplit : ratio ≤ 3 / 8
  · exact cubic_low_endpoint_positive hlower hsplit
  · exact cubic_high_endpoint_positive (le_of_not_ge hsplit) hupper

theorem analytic_cubic_last_strict_upper : lastTransition 3 < (Real.sqrt 3 - 1) / 2 := by
  have hbound : lastTransition 3 ≤ 4 / 11 := by
    apply lastTransition_le_of_nonnegative_bound (by norm_num)
    intro ratio hratio hlower
    rcases lt_or_eq_of_le hratio.2 with hhalf | hhalf
    · exact analytic_cubic_positive_dimension hlower.le hhalf
    · rw [hhalf]
      exact positive_dimH_intersection_half (by norm_num)
  apply hbound.trans_lt
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonnegative := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

end LambdaCantor.Last
