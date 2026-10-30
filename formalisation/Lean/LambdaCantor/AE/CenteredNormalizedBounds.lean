import LambdaCantor.AE.CenteredNormalizedRemainder

noncomputable section
namespace LambdaCantor.AE

/-- Bounds for both derivatives of the normalized Taylor remainder, retaining
the exact powers needed when the normalization exponent is negative. -/
theorem centeredNormalizedRemainder_first_bound
    {parameter displacement velocity exponent scaleExponent bound : ℝ}
    (hpositive : 0 < parameter)
    (hremainder : |centeredTaylorRemainder exponent displacement| ≤ bound * displacement ^ 2)
    (hfirst : |centeredTaylorFirst exponent displacement| ≤ bound * displacement) :
    |scaleExponent * parameter ^ (scaleExponent - 1) *
        centeredTaylorRemainder exponent displacement +
      parameter ^ scaleExponent * centeredTaylorFirst exponent displacement * velocity| ≤
      |scaleExponent| * parameter ^ (scaleExponent - 1) * (bound * displacement ^ 2) +
        parameter ^ scaleExponent * (bound * displacement) * |velocity| := by
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpositive.le _)]
    exact mul_le_mul_of_nonneg_left hremainder (by positivity)
  · rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpositive.le _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hfirst (Real.rpow_nonneg hpositive.le _)) (abs_nonneg _)

theorem centeredNormalizedRemainder_second_bound
    {parameter displacement velocity acceleration exponent scaleExponent bound : ℝ}
    (hpositive : 0 < parameter)
    (hremainder : |centeredTaylorRemainder exponent displacement| ≤ bound * displacement ^ 2)
    (hfirst : |centeredTaylorFirst exponent displacement| ≤ bound * displacement)
    (hsecond : |centeredTaylorSecond exponent displacement| ≤ bound) :
    |scaleExponent * (scaleExponent - 1) * parameter ^ (scaleExponent - 2) *
        centeredTaylorRemainder exponent displacement +
      2 * scaleExponent * parameter ^ (scaleExponent - 1) *
        centeredTaylorFirst exponent displacement * velocity +
      parameter ^ scaleExponent *
        (centeredTaylorSecond exponent displacement * velocity ^ 2 +
          centeredTaylorFirst exponent displacement * acceleration)| ≤
      |scaleExponent * (scaleExponent - 1)| * parameter ^ (scaleExponent - 2) *
        (bound * displacement ^ 2) +
      2 * |scaleExponent| * parameter ^ (scaleExponent - 1) *
        (bound * displacement) * |velocity| +
      parameter ^ scaleExponent * (bound * velocity ^ 2 + bound * displacement * |acceleration|) := by
  apply (abs_add_le _ _).trans
  apply add_le_add
  · apply (abs_add_le _ _).trans
    apply add_le_add
    · rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpositive.le _)]
      exact mul_le_mul_of_nonneg_left hremainder (by positivity)
    · simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hpositive.le _),
        abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfirst (by positivity)) (abs_nonneg _)
  · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hpositive.le _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hpositive.le _)
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg velocity)]
    exact add_le_add
      (mul_le_mul_of_nonneg_right hsecond (sq_nonneg velocity))
      (mul_le_mul_of_nonneg_right hfirst (abs_nonneg acceleration))

end LambdaCantor.AE
