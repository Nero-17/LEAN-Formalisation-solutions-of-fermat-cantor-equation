import LambdaCantor.AE.CenteredTaylor

noncomputable section
open Set

namespace LambdaCantor.AE

theorem centeredTaylorFirst_difference_bound {exponent first second : ℝ}
    (exponent_greater_one : 1 < exponent)
    (first_mem : first ∈ Icc (0 : ℝ) (1/2)) (second_mem : second ∈ Icc (0 : ℝ) (1/2)) :
    |centeredTaylorFirst exponent first - centeredTaylorFirst exponent second| ≤
      (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) * |first-second| := by
  have estimate := (convex_Icc (0 : ℝ) (1/2)).norm_image_sub_le_of_norm_deriv_le
    (fun point membership => (centeredTaylorFirst_hasDerivAt exponent point (by linarith [membership.2])).differentiableAt)
    (fun point membership => by
      rw [(centeredTaylorFirst_hasDerivAt exponent point (by linarith [membership.2])).deriv]
      simpa only [Real.norm_eq_abs] using centeredTaylorSecond_bound exponent_greater_one membership)
    second_mem first_mem
  simpa only [Real.norm_eq_abs] using estimate

theorem centeredTaylorRemainder_difference_bound {exponent first second : ℝ}
    (exponent_greater_one : 1 < exponent)
    (first_mem : first ∈ Icc (0 : ℝ) (1/2)) (second_mem : second ∈ Icc (0 : ℝ) (1/2)) :
    |centeredTaylorRemainder exponent first - centeredTaylorRemainder exponent second| ≤
      (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) *
        max first second * |first-second| := by
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := sub_pos.mpr exponent_greater_one
  have coefficient_nonnegative :
      0 ≤ exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)) := by positivity
  have parameter_bounds : ∀ point ∈ uIcc second first, point ∈ Icc (0 : ℝ) (1/2) := by
    intro point membership
    exact ⟨(le_min second_mem.1 first_mem.1).trans membership.1,
      membership.2.trans (max_le second_mem.2 first_mem.2)⟩
  have estimate := (convex_uIcc second first).norm_image_sub_le_of_norm_deriv_le
    (C := (exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) * max first second)
    (fun point membership => (centeredTaylor_hasDerivAt exponent point
      (by linarith [(parameter_bounds point membership).2])).differentiableAt)
    (fun point membership => by
      rw [(centeredTaylor_hasDerivAt exponent point
        (by linarith [(parameter_bounds point membership).2])).deriv, Real.norm_eq_abs]
      exact (centeredTaylorFirst_bound exponent_greater_one (parameter_bounds point membership)).trans
        (mul_le_mul_of_nonneg_left
          (show point ≤ max first second by simpa only [max_comm] using membership.2)
          coefficient_nonnegative))
    (left_mem_uIcc) (right_mem_uIcc)
  simpa only [Real.norm_eq_abs] using estimate

/-- Difference estimate for the normalized vertical remainder derivative.
The small shared-prefix displacement is preserved in every term, before any
large cylinder-depth coefficient is absorbed by exponential decay. -/
theorem centered_normalized_first_difference_bound
    {exponent parameter scaleExponent first second firstVelocity secondVelocity : ℝ}
    (exponent_greater_one : 1 < exponent) (parameter_positive : 0 < parameter)
    (first_mem : first ∈ Icc (0 : ℝ) (1/2)) (second_mem : second ∈ Icc (0 : ℝ) (1/2)) :
    |(scaleExponent * parameter^(scaleExponent-1) * centeredTaylorRemainder exponent first +
        parameter^scaleExponent * centeredTaylorFirst exponent first * firstVelocity) -
      (scaleExponent * parameter^(scaleExponent-1) * centeredTaylorRemainder exponent second +
        parameter^scaleExponent * centeredTaylorFirst exponent second * secondVelocity)| ≤
      |scaleExponent| * parameter^(scaleExponent-1) *
        ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) * max first second * |first-second|) +
      parameter^scaleExponent *
        (((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) * first) * |firstVelocity-secondVelocity| +
          ((exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2))) * |first-second|) * |secondVelocity|) := by
  have identity :
      (scaleExponent * parameter^(scaleExponent-1) * centeredTaylorRemainder exponent first +
        parameter^scaleExponent * centeredTaylorFirst exponent first * firstVelocity) -
      (scaleExponent * parameter^(scaleExponent-1) * centeredTaylorRemainder exponent second +
        parameter^scaleExponent * centeredTaylorFirst exponent second * secondVelocity) =
      scaleExponent * parameter^(scaleExponent-1) *
        (centeredTaylorRemainder exponent first-centeredTaylorRemainder exponent second) +
      parameter^scaleExponent *
        (centeredTaylorFirst exponent first*(firstVelocity-secondVelocity) +
          (centeredTaylorFirst exponent first-centeredTaylorFirst exponent second)*secondVelocity) := by ring
  rw [identity]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos parameter_positive (scaleExponent-1)),
    abs_of_pos (Real.rpow_pos_of_pos parameter_positive scaleExponent)]
  apply add_le_add
    (mul_le_mul_of_nonneg_left
      (centeredTaylorRemainder_difference_bound exponent_greater_one first_mem second_mem) (by positivity))
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos parameter_positive scaleExponent).le
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (centeredTaylorFirst_bound exponent_greater_one first_mem) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right
      (centeredTaylorFirst_difference_bound exponent_greater_one first_mem second_mem) (abs_nonneg _))

end LambdaCantor.AE
