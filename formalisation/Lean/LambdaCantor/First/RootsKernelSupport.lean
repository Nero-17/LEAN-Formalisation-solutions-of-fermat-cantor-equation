import LambdaCantor.First.RootsKernelScaleBounds

noncomputable section
namespace LambdaCantor.First.Roots

/-- Every unrestricted normalized kernel is supported in one common bounded
interval, obtained from the actual coefficient and address bounds. -/
theorem completeRootKernel_uniform_support {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ (representative tail : ℕ → Bool × Bool) (depth : ℕ),
        |(completeRootKernel data representative depth tail - data.root representative) /
          data.root representative ^ depth| ≤ radius := by
  obtain ⟨lowerScale, upperScale, _, upper_positive, scale_bounds⟩ := rootKernelVertical_uniform_normalization data
  have state_continuous := ((rootFibreData_continuous_state data).snd).abs
  obtain ⟨maximumPoint, _, maximum_property⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set (ℕ → Bool × Bool)).Nonempty) state_continuous.continuousOn
  let slopeBound := |(rootFibreState data maximumPoint).2|
  have slope_nonnegative : 0 ≤ slopeBound := abs_nonneg _
  refine ⟨(slopeBound + 1) * upperScale, mul_pos (by linarith) upper_positive, ?_⟩
  intro representative tail depth
  have ratio_positive : 0 < data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have ratio_less : data.root representative < 1 := by
    linarith [data.upper_lt_half, (data.root_in_band representative).2]
  have coordinate_difference (first second : ℕ → Bool) :
      |address (data.root representative) first - address (data.root representative) second| ≤ 1 := by
    have first_lower := address_nonnegative ratio_positive.le ratio_less first
    have first_upper := address_le_one ratio_positive.le ratio_less first
    have second_lower := address_nonnegative ratio_positive.le ratio_less second
    have second_upper := address_le_one ratio_positive.le ratio_less second
    apply abs_le.mpr
    constructor <;> linarith
  have horizontal_identity : rootKernelHorizontal data representative depth =
      (rootFibreState data representative).2 * rootKernelVertical data representative depth := by
    have ratio := rootKernel_coefficient_ratio data representative depth
    exact (div_eq_iff (rootKernelVertical_ne_zero data representative depth)).mp ratio
  have unscaled : |completeRootKernel data representative depth tail - data.root representative| ≤
      |rootKernelHorizontal data representative depth| + |rootKernelVertical data representative depth| := by
    rw [completeRootKernel_formula]
    change |data.root representative - rootKernelHorizontal data representative depth *
      (address (data.root representative) (fun index => (tail index).1) -
        address (data.root representative) (fun index => (representative (index + depth)).1)) -
      rootKernelVertical data representative depth *
      (address (data.root representative) (fun index => (tail index).2) -
        address (data.root representative) (fun index => (representative (index + depth)).2)) -
      data.root representative| ≤ _
    have triangle := abs_add_le
      (-(rootKernelHorizontal data representative depth *
        (address (data.root representative) (fun index => (tail index).1) -
          address (data.root representative) (fun index => (representative (index + depth)).1))))
      (-(rootKernelVertical data representative depth *
        (address (data.root representative) (fun index => (tail index).2) -
          address (data.root representative) (fun index => (representative (index + depth)).2))))
    have first := mul_le_mul_of_nonneg_left (coordinate_difference
      (fun index => (tail index).1) (fun index => (representative (index + depth)).1))
      (abs_nonneg (rootKernelHorizontal data representative depth))
    have second := mul_le_mul_of_nonneg_left (coordinate_difference
      (fun index => (tail index).2) (fun index => (representative (index + depth)).2))
      (abs_nonneg (rootKernelVertical data representative depth))
    have expression : data.root representative - rootKernelHorizontal data representative depth *
      (address (data.root representative) (fun index => (tail index).1) -
        address (data.root representative) (fun index => (representative (index + depth)).1)) -
      rootKernelVertical data representative depth *
      (address (data.root representative) (fun index => (tail index).2) -
        address (data.root representative) (fun index => (representative (index + depth)).2)) -
      data.root representative =
      -(rootKernelHorizontal data representative depth *
        (address (data.root representative) (fun index => (tail index).1) -
          address (data.root representative) (fun index => (representative (index + depth)).1))) +
      -(rootKernelVertical data representative depth *
        (address (data.root representative) (fun index => (tail index).2) -
          address (data.root representative) (fun index => (representative (index + depth)).2))) := by ring
    rw [expression]
    simp only [abs_neg, abs_mul] at triangle
    exact triangle.trans (by simpa only [mul_one] using add_le_add first second)
  rw [abs_div, abs_of_pos (pow_pos ratio_positive depth)]
  apply (div_le_div_of_nonneg_right unscaled (pow_pos ratio_positive depth).le).trans
  rw [horizontal_identity, abs_mul]
  have identity : (|(rootFibreState data representative).2| * |rootKernelVertical data representative depth| +
      |rootKernelVertical data representative depth|) / data.root representative ^ depth =
      (|(rootFibreState data representative).2| + 1) *
        (|rootKernelVertical data representative depth| / data.root representative ^ depth) := by ring
  rw [identity]
  have vertical_bound := (scale_bounds representative depth).2
  rw [abs_div, abs_of_pos (pow_pos ratio_positive depth)] at vertical_bound
  have slope_bound : |(rootFibreState data representative).2| + 1 ≤ slopeBound + 1 := by
    simpa only [add_comm] using! add_le_add_right (maximum_property (Set.mem_univ representative)) (1 : ℝ)
  exact mul_le_mul slope_bound
    vertical_bound (div_nonneg (abs_nonneg _) (pow_pos ratio_positive depth).le) (by linarith)

end LambdaCantor.First.Roots

