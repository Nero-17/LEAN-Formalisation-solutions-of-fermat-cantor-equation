import LambdaCantor.First.RootsResidualDerivativeBounds

noncomputable section
namespace LambdaCantor.First.Roots

theorem rootFibreData_parameter_taylor {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (digits : ℕ → Bool × Bool) (firstRatio secondRatio : ℝ),
      firstRatio ∈ Set.Icc data.lower data.upper → secondRatio ∈ Set.Icc data.lower data.upper →
      |cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits secondRatio -
        cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits firstRatio -
        deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits) firstRatio *
          (secondRatio - firstRatio)| ≤ constant * |secondRatio - firstRatio| ^ 2 := by
  obtain ⟨constant, constant_nonnegative, derivative_lipschitz⟩ :=
    rootFibreData_residual_derivative_parameter_lipschitz data
  refine ⟨constant, constant_nonnegative, ?_⟩
  intro digits firstRatio secondRatio first_mem second_mem
  have interval_subset : Set.uIcc firstRatio secondRatio ⊆ Set.Icc data.lower data.upper :=
    Set.uIcc_subset_Icc first_mem second_mem
  let residual := cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits
  have differentiable (point : ℝ) (point_mem : point ∈ Set.uIcc firstRatio secondRatio) :
      HasDerivAt residual (deriv residual point) point := by
    have in_band := interval_subset point_mem
    exact (hasDerivAt_cylinderResidual (by linarith [data.lower_gt_quarter, in_band.1])
      (by linarith [data.upper_lt_half, in_band.2]) data.exponent_gt_one.le
      data.leftWord data.rightWord data.leftLength data.rightLength digits).differentiableAt.hasDerivAt
  have distance_bound : ∀ point ∈ Set.uIcc firstRatio secondRatio,
      |point - firstRatio| ≤ |secondRatio - firstRatio| := by
    intro point point_mem
    rcases le_total firstRatio secondRatio with ordered | ordered
    · rw [Set.uIcc_of_le ordered] at point_mem
      rw [abs_of_nonneg (sub_nonneg.mpr point_mem.1), abs_of_nonneg (sub_nonneg.mpr ordered)]
      linarith [point_mem.2]
    · rw [Set.uIcc_of_ge ordered] at point_mem
      rw [abs_of_nonpos (sub_nonpos.mpr point_mem.2), abs_of_nonpos (sub_nonpos.mpr ordered)]
      linarith [point_mem.1]
  have derivative_bound : ∀ point ∈ Set.uIcc firstRatio secondRatio,
      ‖deriv residual point - deriv residual firstRatio‖ ≤ constant * |secondRatio - firstRatio| := by
    intro point point_mem
    rw [Real.norm_eq_abs]
    exact (derivative_lipschitz digits point firstRatio (interval_subset point_mem) first_mem).trans
      (mul_le_mul_of_nonneg_left (distance_bound point point_mem) constant_nonnegative)
  have bound := (convex_uIcc firstRatio secondRatio).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun point point_mem => ((differentiable point point_mem).sub
      (show HasDerivAt (fun argument : ℝ => deriv residual firstRatio * argument)
          (deriv residual firstRatio) point from by
        simpa only [id_eq, mul_one] using!
          ((hasDerivAt_id point).const_mul (deriv residual firstRatio)))).hasDerivWithinAt)
    derivative_bound Set.left_mem_uIcc Set.right_mem_uIcc
  have identity : (residual secondRatio - deriv residual firstRatio * secondRatio) -
      (residual firstRatio - deriv residual firstRatio * firstRatio) =
      residual secondRatio - residual firstRatio - deriv residual firstRatio * (secondRatio - firstRatio) := by ring
  simp only [Pi.sub_apply] at bound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, identity] at bound
  change |residual secondRatio - residual firstRatio - deriv residual firstRatio * (secondRatio - firstRatio)| ≤ _
  nlinarith [bound]

end LambdaCantor.First.Roots
