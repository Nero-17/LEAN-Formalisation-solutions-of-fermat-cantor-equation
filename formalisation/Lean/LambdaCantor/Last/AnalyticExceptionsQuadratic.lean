import LambdaCantor.Last.AnalyticExceptionsCubic

noncomputable section
namespace LambdaCantor.Last

theorem quadratic_low_endpoint_positive {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ 147 / 400) :
    0 < dimH (intersection 2 ratio) := by
  have hpositive : 0 < ratio := by linarith
  have hhalf : ratio < 1 / 2 := by linarith
  have hcomplement : 0 < 1 - ratio := by linarith
  have hgeometry := quadratic_low_source_geometry hlower hupper
  dsimp only at hgeometry
  have hfirst : 0 < 1 - ratio + ratio ^ 3 - ratio ^ 4 := by
    nlinarith [mul_pos (pow_pos hpositive 3) (show 0 < 1 - ratio by linarith)]
  have hfirst_upper : 0 < 1 - ratio + ratio ^ 3 := by nlinarith [pow_pos hpositive 3]
  let source : EndpointRectangle 2 ratio := {
    firstWord := [true, false, false, true]
    secondWord := [true, false, false]
    firstOffset := 0
    secondOffset := 1
    first_positive := by dsimp [scalarWordMap]; nlinarith [hfirst]
    second_positive := by dsimp [scalarWordMap]; linarith
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
    ring_nf <;> field_simp [hcomplement.ne', hfirst_upper.ne'] <;> ring

theorem quadratic_middle_endpoint_positive {ratio : ℝ}
    (hlower : (147 / 400 : ℝ) ≤ ratio) (hupper : ratio ≤ 3 / 8) :
    0 < dimH (intersection 2 ratio) := by
  have hpositive : 0 < ratio := by linarith
  have hhalf : ratio < 1 / 2 := by linarith
  have hcomplement : 0 < 1 - ratio := by linarith
  have hgeometry := quadratic_middle_source_geometry hlower hupper
  dsimp only at hgeometry
  have hfirst : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hpositive) (show 0 < 1 - ratio by linarith)]
  have hfirst_upper : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 + ratio ^ 4 := by positivity
  let source : EndpointRectangle 2 ratio := {
    firstWord := [true, false, true, false]
    secondWord := [true, false, true]
    firstOffset := 0
    secondOffset := 1
    first_positive := by dsimp [scalarWordMap]; nlinarith [hfirst]
    second_positive := by dsimp [scalarWordMap]; nlinarith [hfirst]
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
    ring_nf <;> field_simp [hcomplement.ne', hfirst_upper.ne'] <;> ring

theorem quadratic_high_endpoint_positive {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio < 1 / 2) :
    0 < dimH (intersection 2 ratio) := by
  have hpositive : 0 < ratio := by linarith
  have hcomplement : 0 < 1 - ratio := by linarith
  have hgeometry := quadratic_high_source_geometry hlower hupper
  dsimp only at hgeometry
  have hfirst : 0 < 1 - ratio + ratio ^ 2 - ratio ^ 3 := by
    nlinarith [mul_pos (sq_pos_of_pos hpositive) (show 0 < 1 - ratio by linarith)]
  have hfirst_upper : 0 < 1 - ratio + ratio ^ 2 := by nlinarith [sq_nonneg ratio]
  let source : EndpointRectangle 2 ratio := {
    firstWord := [true, false, true]
    secondWord := [true, false]
    firstOffset := 0
    secondOffset := 1
    first_positive := by dsimp [scalarWordMap]; nlinarith [hfirst]
    second_positive := by dsimp [scalarWordMap]; linarith
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
    ring_nf <;> field_simp [hcomplement.ne', hfirst_upper.ne'] <;> ring

theorem analytic_quadratic_positive_dimension {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio < 1 / 2) :
    0 < dimH (intersection 2 ratio) := by
  by_cases hfirst : ratio ≤ 147 / 400
  · exact quadratic_low_endpoint_positive hlower hfirst
  · by_cases hsecond : ratio ≤ 3 / 8
    · exact quadratic_middle_endpoint_positive (le_of_not_ge hfirst) hsecond
    · exact quadratic_high_endpoint_positive (le_of_not_ge hsecond) hupper

theorem analytic_quadratic_last_strict_upper : lastTransition 2 < (Real.sqrt 3 - 1) / 2 := by
  have hbound : lastTransition 2 ≤ 4 / 11 := by
    apply lastTransition_le_of_nonnegative_bound (by norm_num)
    intro ratio hratio hlower
    rcases lt_or_eq_of_le hratio.2 with hhalf | hhalf
    · exact analytic_quadratic_positive_dimension hlower.le hhalf
    · rw [hhalf]
      exact positive_dimH_intersection_half (by norm_num)
  apply hbound.trans_lt
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonnegative := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

end LambdaCantor.Last
