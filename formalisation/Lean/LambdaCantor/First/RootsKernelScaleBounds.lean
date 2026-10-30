import LambdaCantor.First.RootsKernelState

noncomputable section
namespace LambdaCantor.First.Roots

theorem rootKernelVertical_depth {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    rootKernelVertical data representative depth =
      rootKernelVertical data representative 0 * data.root representative ^ depth := by
  unfold rootKernelVertical
  rw [Nat.add_zero, pow_add]
  ring

theorem continuous_rootKernelVertical_zero {exponent : ℝ} (data : RootFibreData exponent) :
    Continuous (fun representative => rootKernelVertical data representative 0) := by
  have root_continuous := rootFibreData_continuous_root data
  have derivative_continuous := (rootFibreData_continuous_residual_derivative data).comp
    (continuous_id.prodMk (root_continuous.subtype_mk data.root_in_band))
  have incidence_continuous := continuous_cylinderIncidencePoint
    (show 0 ≤ data.lower by linarith [data.lower_gt_quarter])
    (show data.upper < 1 by linarith [data.upper_lt_half]) data.ordered
    data.root root_continuous data.root_in_band data.leftWord data.rightWord
    data.leftLength data.rightLength
  have coordinate_continuous : Continuous (fun representative =>
      cylinderCoordinate data.rightWord data.rightLength (fun index => (representative index).2)
        (data.root representative)) := by
    convert continuous_snd.comp (continuous_snd.comp incidence_continuous) using 1
    funext representative
    exact (cylinder_address
      (show 0 ≤ data.root representative by linarith [data.lower_gt_quarter, (data.root_in_band representative).1])
      (show data.root representative < 1 by linarith [data.upper_lt_half, (data.root_in_band representative).2])
      data.rightWord data.rightLength (fun index => (representative index).2)).symm
  have derivative_nonzero (representative : ℕ → Bool × Bool) :
      deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative)
        (data.root representative) ≠ 0 := by
    intro zero
    have bound := data.transverse representative
    rw [zero, abs_zero] at bound
    linarith [data.derivative_lower_bound_positive]
  exact ((continuous_const.mul (coordinate_continuous.rpow_const
    (fun _ => Or.inr (show 0 ≤ exponent - 1 by linarith [data.exponent_gt_one])))).mul
      (root_continuous.pow (data.rightLength + 0))).div derivative_continuous derivative_nonzero

/-- After division by the natural cylinder scale, every actual kernel dilation
lies in one common compact subset of the nonzero real numbers. -/
theorem rootKernelVertical_uniform_normalization {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ lowerScale upperScale : ℝ, 0 < lowerScale ∧ 0 < upperScale ∧
      ∀ (representative : ℕ → Bool × Bool) (depth : ℕ),
        lowerScale ≤ |rootKernelVertical data representative depth / data.root representative ^ depth| ∧
        |rootKernelVertical data representative depth / data.root representative ^ depth| ≤ upperScale := by
  have absolute_continuous := (continuous_rootKernelVertical_zero data).abs
  obtain ⟨minimumPoint, _, minimum_property⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (ℕ → Bool × Bool)).Nonempty) absolute_continuous.continuousOn
  obtain ⟨maximumPoint, _, maximum_property⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (ℕ → Bool × Bool)).Nonempty) absolute_continuous.continuousOn
  refine ⟨|rootKernelVertical data minimumPoint 0|, |rootKernelVertical data maximumPoint 0|,
    abs_pos.mpr (rootKernelVertical_ne_zero data minimumPoint 0),
    abs_pos.mpr (rootKernelVertical_ne_zero data maximumPoint 0), ?_⟩
  intro representative depth
  have ratio_nonzero : data.root representative ≠ 0 := by
    have : 0 < data.root representative := by
      linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
    exact this.ne'
  have normalization :
      rootKernelVertical data representative depth / data.root representative ^ depth =
        rootKernelVertical data representative 0 := by
    rw [rootKernelVertical_depth data representative depth]
    exact mul_div_cancel_right₀ _ (pow_ne_zero depth ratio_nonzero)
  simpa only [normalization, Set.mem_setOf_eq] using
    And.intro (minimum_property (Set.mem_univ representative))
      (maximum_property (Set.mem_univ representative))

end LambdaCantor.First.Roots
