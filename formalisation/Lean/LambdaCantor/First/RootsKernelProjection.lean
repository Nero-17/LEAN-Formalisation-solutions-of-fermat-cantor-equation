import LambdaCantor.First.RootsKernelLaws
import LambdaCantor.Addresses

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

def complementFirst (digits : ℕ → Bool × Bool) : ℕ → Bool × Bool :=
  fun index => (!(digits index).1, (digits index).2)

theorem continuous_complementFirst : Continuous complementFirst := by
  apply continuous_pi
  intro index
  exact (continuous_of_discreteTopology :
    Continuous (fun digit : Bool × Bool => (!digit.1, digit.2))).comp
      (continuous_apply index)

theorem complementFirst_preserves_measure : pairedAddressMeasure.map complementFirst = pairedAddressMeasure := by
  let complement : Bool ≃ Bool :=
    { toFun := Bool.not
      invFun := Bool.not
      left_inv := fun digit => by cases digit <;> rfl
      right_inv := fun digit => by cases digit <;> rfl }
  have digit_invariant : (PMF.uniformOfFintype (Bool × Bool)).toMeasure.map
      (fun digit : Bool × Bool => (!digit.1, digit.2)) = (PMF.uniformOfFintype (Bool × Bool)).toMeasure := by
    rw [LambdaCantor.First.PrefixSlopes.uniform_paired_measure_eq_sum,
      Measure.map_sum (by fun_prop)]
    simp_rw [Measure.map_smul, Measure.map_dirac]
    rw [Measure.sum_fintype, Measure.sum_fintype]
    exact (Equiv.prodCongr complement (Equiv.refl Bool)).sum_comp
      (fun digit => (4 : ℝ≥0∞)⁻¹ • Measure.dirac digit)
  unfold pairedAddressMeasure complementFirst
  rw [Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => (PMF.uniformOfFintype (Bool × Bool)).toMeasure)
    (f := fun (_ : ℕ) (digit : Bool × Bool) => (!digit.1, digit.2))
    (fun _ => (continuous_of_discreteTopology :
      Continuous (fun digit : Bool × Bool => (!digit.1, digit.2))).measurable)]
  simp_rw [digit_invariant]

/-- Complementing the first fair coordinate converts a sum of the two Cantor
coordinates into the positive-slope projection used by linear regularity. -/
theorem affine_address_sum_law {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (center horizontal vertical : ℝ) (vertical_nonzero : vertical ≠ 0) :
    pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool => center -
      horizontal * address ratio (fun index => (digits index).1) -
      vertical * address ratio (fun index => (digits index).2)) =
      (LambdaCantor.First.PrefixSlopes.projectedMeasure ratio (horizontal / vertical)).map
        (fun value => center - horizontal - vertical * value) := by
  have sum_measurable : Measurable (fun digits : ℕ → Bool × Bool => center -
      horizontal * address ratio (fun index => (digits index).1) -
      vertical * address ratio (fun index => (digits index).2)) := by
    have address_measurable := (continuous_address nonnegative less_one).measurable
    exact (measurable_const.sub (measurable_const.mul (address_measurable.comp (by fun_prop)))).sub
      (measurable_const.mul (address_measurable.comp (by fun_prop)))
  conv_lhs => rw [← complementFirst_preserves_measure]
  rw [Measure.map_map sum_measurable continuous_complementFirst.measurable]
  unfold LambdaCantor.First.PrefixSlopes.projectedMeasure
  rw [Measure.map_map (by fun_prop)
    (LambdaCantor.First.PrefixSlopes.projectedAddress_measurable nonnegative less_one)]
  congr 1
  funext digits
  dsimp [Function.comp_def, complementFirst, LambdaCantor.First.PrefixSlopes.projectedAddress]
  rw [address_complement nonnegative less_one]
  field_simp [vertical_nonzero]
  <;> ring


def rootKernelHorizontal {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) : ℝ :=
  exponent * cylinderCoordinate data.leftWord data.leftLength (fun index => (representative index).1)
    (data.root representative) ^ (exponent - 1) * data.root representative ^ (data.leftLength + depth) /
      deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative)
        (data.root representative)

def rootKernelVertical {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) : ℝ :=
  exponent * cylinderCoordinate data.rightWord data.rightLength (fun index => (representative index).2)
    (data.root representative) ^ (exponent - 1) * data.root representative ^ (data.rightLength + depth) /
      deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative)
        (data.root representative)

theorem rootKernelVertical_ne_zero {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) : rootKernelVertical data representative depth ≠ 0 := by
  have ratio_positive : 0 < data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have derivative_nonzero : deriv (cylinderResidual exponent data.leftWord data.rightWord
      data.leftLength data.rightLength representative) (data.root representative) ≠ 0 := by
    intro zero
    have bound := data.transverse representative
    rw [zero, abs_zero] at bound
    linarith [data.derivative_lower_bound_positive]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by linarith [data.exponent_gt_one])
      (Real.rpow_pos_of_pos (data.right_positive representative _ (data.root_in_band representative)) _).ne')
      (pow_pos ratio_positive _).ne') derivative_nonzero

theorem completeRootKernelLaw_projected {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    completeRootKernelLaw data representative depth =
      (LambdaCantor.First.PrefixSlopes.projectedMeasure (data.root representative)
        (rootKernelHorizontal data representative depth / rootKernelVertical data representative depth)).map
        (fun value => data.root representative +
          rootKernelHorizontal data representative depth *
            address (data.root representative) (fun index => (representative (index + depth)).1) +
          rootKernelVertical data representative depth *
            address (data.root representative) (fun index => (representative (index + depth)).2) -
          rootKernelHorizontal data representative depth - rootKernelVertical data representative depth * value) := by
  have ratio_nonnegative : 0 ≤ data.root representative := by
    linarith [data.lower_gt_quarter, (data.root_in_band representative).1]
  have ratio_less : data.root representative < 1 := by
    linarith [data.upper_lt_half, (data.root_in_band representative).2]
  rw [← affine_address_sum_law ratio_nonnegative ratio_less _ _ _ (rootKernelVertical_ne_zero data representative depth)]
  unfold completeRootKernelLaw
  congr 1
  funext tail
  rw [completeRootKernel_formula]
  dsimp [rootKernelHorizontal, rootKernelVertical]
  ring

end LambdaCantor.First.Roots

