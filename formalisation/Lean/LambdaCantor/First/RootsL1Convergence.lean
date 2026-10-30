import LambdaCantor.First.RootsL1Refinement

noncomputable section
open MeasureTheory Filter Topology
namespace LambdaCantor.First.Roots

theorem goodSetKernelLaw_mass {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) :
    (goodSetKernelLaw data orderIndex bound depth).real Set.univ =
      pairedAddressMeasure.real
        (prefixNeighborhood (rootSobolevGoodSet data orderIndex bound) depth) := by
  unfold goodSetKernelLaw
  rw [measureReal_def, Measure.map_apply (continuous_selectedRootKernel data _ depth).measurable
    MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
  rfl

/-- The actual density sequence on each compact Sobolev sublevel converges in
L1. Pair replacement and deletion bounds have all been discharged internally. -/
theorem rootSobolevGoodSet_actual_L1_convergence
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∃ density : Lp ℝ 1 volume,
      Tendsto (goodSetKernelDensityL1 data orderIndex bound) atTop (𝓝 density) := by
  obtain ⟨prefactor, displacementConstant, prefactor_nonnegative, displacement_positive,
    minimumDepth, replacements⟩ := rootSobolevGoodSet_retained_L1_replacement data orderIndex bound
  let selected := rootSobolevGoodSet data orderIndex bound
  let rate := fun depth : ℕ => prefactor *
    (displacementConstant * ((depth : ℝ) + 1) * data.upper ^ depth) ^
      (2 * (1 / ((orderIndex : ℝ) + 1)) / (3 + 2 * (1 / ((orderIndex : ℝ) + 1))))
  let massLoss := fun depth : ℕ => pairedAddressMeasure.real (prefixNeighborhood selected depth) -
    pairedAddressMeasure.real (prefixNeighborhood selected (depth + 1))
  have upper_nonnegative : 0 ≤ data.upper := by linarith [data.lower_gt_quarter, data.ordered]
  have upper_lt_one : data.upper < 1 := by linarith [data.upper_lt_half]
  have exponent_bounds := interpolation_exponent_bounds (1 / ((orderIndex : ℝ) + 1)) (by positivity)
  have rate_summable : Summable rate := summable_actual_replacement_rate data.upper _ prefactor
    displacementConstant upper_nonnegative upper_lt_one exponent_bounds.1 exponent_bounds.2
    displacement_positive.le
  have losses_summable : Summable massLoss := prefixNeighborhood_deleted_mass_summable selected
  have step_bound (depth : ℕ) (depth_ge : minimumDepth ≤ depth) :
      ‖goodSetKernelDensityL1 data orderIndex bound (depth + 1) -
        goodSetKernelDensityL1 data orderIndex bound depth‖ ≤ massLoss depth + rate depth := by
    obtain ⟨retained_exists, replacement_bound⟩ := replacements depth depth_ge
    have dominated : (pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth) ≤ goodSetKernelLaw data orderIndex bound depth := by
      exact Measure.map_mono
        (Measure.restrict_mono_set _ (prefixNeighborhood_antitone selected (Nat.le_succ depth)))
        (continuous_selectedRootKernel data selected depth).measurable
    have deletion_cost := measureDensityL1_distance_of_le retained_exists
      (rootSobolevGoodSet_kernel_sum_density data orderIndex bound depth) dominated
    change ‖goodSetKernelDensityL1 data orderIndex bound depth - measureDensityL1 _ retained_exists‖ =
      (goodSetKernelLaw data orderIndex bound depth).real Set.univ -
        ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
          (selectedRootKernel data selected depth)).real Set.univ at deletion_cost
    rw [goodSetKernelLaw_mass] at deletion_cost
    have retained_mass : ((pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
        (selectedRootKernel data selected depth)).real Set.univ =
        pairedAddressMeasure.real (prefixNeighborhood selected (depth + 1)) := by
      rw [measureReal_def, Measure.map_apply (continuous_selectedRootKernel data selected depth).measurable
        MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ]
      rfl
    rw [retained_mass] at deletion_cost
    calc
      _ ≤ ‖goodSetKernelDensityL1 data orderIndex bound (depth + 1) -
          measureDensityL1 _ retained_exists‖ +
          ‖measureDensityL1 _ retained_exists - goodSetKernelDensityL1 data orderIndex bound depth‖ := by
        simpa only [dist_eq_norm] using (dist_triangle
          (goodSetKernelDensityL1 data orderIndex bound (depth + 1))
          (measureDensityL1 _ retained_exists) (goodSetKernelDensityL1 data orderIndex bound depth))
      _ ≤ rate depth + massLoss depth := by
        apply add_le_add replacement_bound
        rw [norm_sub_rev]
        exact deletion_cost.le
      _ = _ := add_comm _ _
  have shifted_cauchy : CauchySeq (fun depth =>
      goodSetKernelDensityL1 data orderIndex bound (depth + minimumDepth)) := by
    apply cauchySeq_of_dist_le_of_summable (fun depth =>
      massLoss (depth + minimumDepth) + rate (depth + minimumDepth))
    · intro depth
      rw [dist_comm, dist_eq_norm]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        step_bound (depth + minimumDepth) (by omega)
    · exact (summable_nat_add_iff minimumDepth).mpr (losses_summable.add rate_summable)
  obtain ⟨density, convergence⟩ := cauchySeq_tendsto_of_complete shifted_cauchy
  exact ⟨density, (tendsto_add_atTop_iff_nat minimumDepth).mp convergence⟩

end LambdaCantor.First.Roots
