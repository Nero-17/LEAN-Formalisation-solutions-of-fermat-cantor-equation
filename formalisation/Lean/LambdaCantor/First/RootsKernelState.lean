import LambdaCantor.First.RootsKernelProjection
import LambdaCantor.First.RootsStateNull
import LambdaCantor.First.SobolevEnergyContinuity

noncomputable section
namespace LambdaCantor.First.Roots

/-- The projection slope of every actual frozen kernel is exactly the state
slope. In particular the slope is independent of the refinement depth. -/
theorem rootKernel_coefficient_ratio {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    rootKernelHorizontal data representative depth / rootKernelVertical data representative depth =
      (rootFibreState data representative).2 := by
  have ratio_positive : 0 < data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have ratio_less : data.root representative < 1 := by
    linarith [data.upper_lt_half, (data.root_in_band representative).2]
  have left_positive := data.left_positive representative _ (data.root_in_band representative)
  have right_positive := data.right_positive representative _ (data.root_in_band representative)
  have exponent_nonzero : exponent ≠ 0 := by linarith [data.exponent_gt_one]
  have derivative_nonzero : deriv (cylinderResidual exponent data.leftWord data.rightWord
      data.leftLength data.rightLength representative) (data.root representative) ≠ 0 := by
    intro zero
    have bound := data.transverse representative
    rw [zero, abs_zero] at bound
    linarith [data.derivative_lower_bound_positive]
  have right_power_nonzero := (Real.rpow_pos_of_pos right_positive (exponent - 1)).ne'
  unfold rootFibreState incidenceState cylinderIncidencePoint
  simp only [cylinder_address ratio_positive.le ratio_less]
  change rootKernelHorizontal data representative depth / rootKernelVertical data representative depth =
    data.root representative ^ ((data.leftLength : ℝ) - data.rightLength) *
      (cylinderCoordinate data.leftWord data.leftLength (fun index => (representative index).1)
          (data.root representative) /
        cylinderCoordinate data.rightWord data.rightLength (fun index => (representative index).2)
          (data.root representative)) ^ (exponent - 1)
  rw [Real.rpow_sub ratio_positive, Real.rpow_natCast, Real.rpow_natCast,
    Real.div_rpow left_positive.le right_positive.le]
  unfold rootKernelHorizontal rootKernelVertical
  simp only [pow_add]
  field_simp [exponent_nonzero, derivative_nonzero, right_power_nonzero, ratio_positive.ne']
  <;> ring


/-- Direct identification with the plus-sign model defining the actual good-set
Sobolev energy; no sign convention is silently changed. -/
theorem completeRootKernelLaw_rootModel {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    completeRootKernelLaw data representative depth =
      (pairedAddressMeasure.map (projectedRootModel (rootFibreState data representative))).map
        (fun value => data.root representative +
          rootKernelHorizontal data representative depth *
            address (data.root representative) (fun index => (representative (index + depth)).1) +
          rootKernelVertical data representative depth *
            address (data.root representative) (fun index => (representative (index + depth)).2) -
          rootKernelVertical data representative depth * value) := by
  have ratio_nonnegative : 0 ≤ data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have ratio_less : data.root representative < 1 := by
    linarith [data.upper_lt_half, (data.root_in_band representative).2]
  have model_measurable : Measurable (projectedRootModel (rootFibreState data representative)) := by
    have address_measurable := (continuous_address ratio_nonnegative ratio_less).measurable
    exact (measurable_const.mul (address_measurable.comp (by fun_prop))).add
      (address_measurable.comp (by fun_prop))
  rw [MeasureTheory.Measure.map_map (by fun_prop) model_measurable]
  unfold completeRootKernelLaw
  congr 1
  funext tail
  rw [completeRootKernel_formula]
  change _ = data.root representative +
    rootKernelHorizontal data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).1) +
    rootKernelVertical data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).2) -
    rootKernelVertical data representative depth *
      ((rootFibreState data representative).2 * address (data.root representative) (fun index => (tail index).1) +
        address (data.root representative) (fun index => (tail index).2))
  rw [← rootKernel_coefficient_ratio data representative depth]
  have vertical_nonzero := rootKernelVertical_ne_zero data representative depth
  change data.root representative - rootKernelHorizontal data representative depth *
    (address (data.root representative) (fun index => (tail index).1) -
      address (data.root representative) (fun index => (representative (index + depth)).1)) -
    rootKernelVertical data representative depth *
    (address (data.root representative) (fun index => (tail index).2) -
      address (data.root representative) (fun index => (representative (index + depth)).2)) = _
  field_simp [vertical_nonzero]
  <;> ring
end LambdaCantor.First.Roots

