import LambdaCantor.First.RootsCoordinateBounds

noncomputable section
namespace LambdaCantor.First.Roots

theorem rpow_linearization_positive_band {lowerCoordinate exponent left right : ℝ}
    (lower_positive : 0 < lowerCoordinate)
    (left_mem : left ∈ Set.Icc lowerCoordinate 1) (right_mem : right ∈ Set.Icc lowerCoordinate 1) :
    |right ^ exponent - left ^ exponent - exponent * left ^ (exponent - 1) * (right - left)| ≤
      (|exponent| * (|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2)))) * |right - left| ^ 2 := by
  have interval_subset : Set.uIcc left right ⊆ Set.Icc lowerCoordinate 1 :=
    Set.uIcc_subset_Icc left_mem right_mem
  have distance_bound : ∀ point ∈ Set.uIcc left right, |point - left| ≤ |right - left| := by
    intro point point_mem
    rcases le_total left right with ordered | ordered
    · rw [Set.uIcc_of_le ordered] at point_mem
      rw [abs_of_nonneg (sub_nonneg.mpr point_mem.1), abs_of_nonneg (sub_nonneg.mpr ordered)]
      linarith [point_mem.2]
    · rw [Set.uIcc_of_ge ordered] at point_mem
      rw [abs_of_nonpos (sub_nonpos.mpr point_mem.2), abs_of_nonpos (sub_nonpos.mpr ordered)]
      linarith [point_mem.1]
  have derivative : ∀ point ∈ Set.uIcc left right,
      HasDerivAt (fun point : ℝ => point ^ exponent - exponent * left ^ (exponent - 1) * point)
        (exponent * point ^ (exponent - 1) - exponent * left ^ (exponent - 1)) point := by
    intro point point_mem
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lower_positive.trans_le (interval_subset point_mem).1)))).sub
      (by simpa only [id_eq, mul_one] using!
        ((hasDerivAt_id point).const_mul (exponent * left ^ (exponent - 1))))
  have derivative_bound : ∀ point ∈ Set.uIcc left right,
      ‖exponent * point ^ (exponent - 1) - exponent * left ^ (exponent - 1)‖ ≤
        (|exponent| * (|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2)))) * |right - left| := by
    intro point point_mem
    have power_bound := rpow_lipschitz_positive_band (exponent := exponent - 1)
      lower_positive (interval_subset point_mem) left_mem
    have exponent_identity : exponent - 1 - 1 = exponent - 2 := by ring
    rw [exponent_identity] at power_bound
    have scaled_bound := mul_le_mul_of_nonneg_left power_bound (abs_nonneg exponent)
    have coefficient_nonnegative : 0 ≤ |exponent| *
        (|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2))) := by positivity
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    exact scaled_bound.trans (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (distance_bound point point_mem) coefficient_nonnegative)
  have bound := (convex_uIcc left right).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun point point_mem => (derivative point point_mem).hasDerivWithinAt) derivative_bound
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have identity : (right ^ exponent - exponent * left ^ (exponent - 1) * right) -
      (left ^ exponent - exponent * left ^ (exponent - 1) * left) =
      right ^ exponent - left ^ exponent - exponent * left ^ (exponent - 1) * (right - left) := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, identity] at bound
  nlinarith [bound]

end LambdaCantor.First.Roots
