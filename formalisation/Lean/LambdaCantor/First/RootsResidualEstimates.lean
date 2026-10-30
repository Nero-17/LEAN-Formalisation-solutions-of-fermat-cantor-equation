import LambdaCantor.First.RootFibreGeometry
import LambdaCantor.First.PrefixEstimates
import LambdaCantor.First.AddressDerivativeContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace LambdaCantor.First.Roots

theorem cylinderCoordinate_shared_prefix_bound {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (word : ℕ → Bool) (length depth : ℕ) (left right : ℕ → Bool)
    (agreement : ∀ index < depth, left index = right index) :
    |cylinderCoordinate word length left ratio - cylinderCoordinate word length right ratio| ≤
      ratio ^ length * ratio ^ depth := by
  have identity : cylinderCoordinate word length left ratio -
      cylinderCoordinate word length right ratio =
      ratio ^ length * (address ratio left - address ratio right) := by
    unfold cylinderCoordinate
    ring
  rw [identity, abs_mul, abs_of_nonneg (pow_nonneg nonnegative length)]
  exact mul_le_mul_of_nonneg_left
    (address_shared_prefix_bound nonnegative less_one left right depth agreement)
    (pow_nonneg nonnegative length)

theorem rpow_lipschitz_unit_interval {exponent left right : ℝ}
    (exponent_ge_one : 1 ≤ exponent) (left_mem : left ∈ Set.Icc (0 : ℝ) 1)
    (right_mem : right ∈ Set.Icc (0 : ℝ) 1) :
    |left ^ exponent - right ^ exponent| ≤ exponent * |left - right| := by
  have derivative (point : ℝ) := Real.hasDerivAt_rpow_const (x := point) (Or.inr exponent_ge_one)
  have derivative_bound : ∀ point ∈ Set.Icc (0 : ℝ) 1,
      ‖exponent * point ^ (exponent - 1)‖ ≤ exponent := by
    intro point point_mem
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg point_mem.1 _))]
    have bound := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one point_mem.1 point_mem.2 (by linarith : 0 ≤ exponent - 1))
      (show 0 ≤ exponent by linarith)
    simpa only [mul_one] using bound
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun point _ => (derivative point).hasDerivWithinAt) derivative_bound right_mem left_mem

/-- A genuine residual estimate for the manuscript's root data: paired tails
with a shared depth-j prefix change the residual by at most 2*n*lambda^j
at one common parameter. -/
theorem rootFibreData_residual_shared_prefix_bound {exponent : ℝ}
    (data : RootFibreData exponent) (ratio : ℝ) (in_band : ratio ∈ Set.Icc data.lower data.upper)
    (left right : ℕ → Bool × Bool) (depth : ℕ)
    (agreement : ∀ index < depth, left index = right index) :
    |cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength left ratio -
      cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength right ratio| ≤
      2 * exponent * ratio ^ depth := by
  have ratio_nonnegative : 0 ≤ ratio := by linarith [data.lower_gt_quarter, in_band.1]
  have ratio_lt_one : ratio < 1 := by linarith [data.upper_lt_half, in_band.2]
  have coordinate_mem (word : ℕ → Bool) (length : ℕ) (digits : ℕ → Bool) :
      cylinderCoordinate word length digits ratio ∈ Set.Icc (0 : ℝ) 1 := by
    unfold cylinderCoordinate
    rw [← cylinder_address ratio_nonnegative ratio_lt_one word length digits]
    exact ⟨address_nonnegative ratio_nonnegative ratio_lt_one _,
      address_le_one ratio_nonnegative ratio_lt_one _⟩
  have coordinate_bound (word : ℕ → Bool) (length : ℕ) (coordinate : Bool × Bool → Bool) :
      |cylinderCoordinate word length (fun index => coordinate (left index)) ratio ^ exponent -
        cylinderCoordinate word length (fun index => coordinate (right index)) ratio ^ exponent| ≤
        exponent * ratio ^ depth := by
    have power_bound := rpow_lipschitz_unit_interval data.exponent_gt_one.le
      (coordinate_mem word length (fun index => coordinate (left index)))
      (coordinate_mem word length (fun index => coordinate (right index)))
    have tail_bound := cylinderCoordinate_shared_prefix_bound ratio_nonnegative ratio_lt_one word
      length depth (fun index => coordinate (left index)) (fun index => coordinate (right index))
      (fun index index_lt => congrArg coordinate (agreement index index_lt))
    have contraction_bound : ratio ^ length ≤ 1 := pow_le_one₀ ratio_nonnegative ratio_lt_one.le
    have scaled_bound := mul_le_mul_of_nonneg_right contraction_bound (pow_nonneg ratio_nonnegative depth)
    have total := power_bound.trans (mul_le_mul_of_nonneg_left
      (tail_bound.trans (by simpa only [one_mul] using scaled_bound))
      (show 0 ≤ exponent by linarith [data.exponent_gt_one]))
    exact total
  have left_bound := coordinate_bound data.leftWord data.leftLength Prod.fst
  have right_bound := coordinate_bound data.rightWord data.rightLength Prod.snd
  unfold cylinderResidual
  have identity : ∀ a b c d : ℝ, (a + b - 1) - (c + d - 1) = (a - c) + (b - d) := by
    intros
    ring
  rw [identity]
  exact (abs_add_le _ _).trans (by linarith)

theorem hasDerivAt_cylinderCoordinate {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (word : ℕ → Bool) (length : ℕ) (digits : ℕ → Bool) :
    HasDerivAt (cylinderCoordinate word length digits)
      (addressParameterDerivative ratio (cylinderDigits word length digits)) ratio := by
  apply (hasDerivAt_address_parameter positive less_one (cylinderDigits word length digits)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Set.Ioo (0 : ℝ) 1 from ⟨positive, less_one⟩)]
    with parameter parameter_mem
  exact (cylinder_address parameter_mem.1.le parameter_mem.2 word length digits).symm

def cylinderResidualDerivative (exponent : ℝ) (leftWord rightWord : ℕ → Bool)
    (leftLength rightLength : ℕ) (digits : ℕ → Bool × Bool) (ratio : ℝ) : ℝ :=
  addressParameterDerivative ratio (cylinderDigits leftWord leftLength (fun index => (digits index).1)) *
      exponent * cylinderCoordinate leftWord leftLength (fun index => (digits index).1) ratio ^ (exponent - 1) +
    addressParameterDerivative ratio (cylinderDigits rightWord rightLength (fun index => (digits index).2)) *
      exponent * cylinderCoordinate rightWord rightLength (fun index => (digits index).2) ratio ^ (exponent - 1)

theorem hasDerivAt_cylinderResidual {ratio exponent : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1) (exponent_ge_one : 1 ≤ exponent)
    (leftWord rightWord : ℕ → Bool) (leftLength rightLength : ℕ) (digits : ℕ → Bool × Bool) :
    HasDerivAt (cylinderResidual exponent leftWord rightWord leftLength rightLength digits)
      (cylinderResidualDerivative exponent leftWord rightWord leftLength rightLength digits ratio) ratio := by
  exact (((hasDerivAt_cylinderCoordinate positive less_one leftWord leftLength
    (fun index => (digits index).1)).rpow_const (Or.inr exponent_ge_one)).add
      ((hasDerivAt_cylinderCoordinate positive less_one rightWord rightLength
        (fun index => (digits index).2)).rpow_const (Or.inr exponent_ge_one))).sub_const 1

/-- Joint continuity is proved for the actual derivative, uniformly over both
complete tail addresses and the whole compact parameter band. -/
theorem rootFibreData_continuous_residual_derivative {exponent : ℝ} (data : RootFibreData exponent) :
    Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc data.lower data.upper =>
      deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength
        point.1) point.2) := by
  have lower_nonnegative : 0 ≤ data.lower := by linarith [data.lower_gt_quarter]
  have upper_lt_one : data.upper < 1 := by linarith [data.upper_lt_half]
  have address_continuous := continuous_address_band lower_nonnegative upper_lt_one data.ordered
  have derivative_continuous := continuous_addressParameterDerivative_band lower_nonnegative
    upper_lt_one data.ordered
  have coordinate_continuous (word : ℕ → Bool) (length : ℕ) (coordinate : Bool × Bool → Bool)
      (continuous_coordinate : Continuous coordinate) :
      Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc data.lower data.upper =>
        cylinderCoordinate word length (fun index => coordinate (point.1 index)) point.2) ∧
      Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc data.lower data.upper =>
        addressParameterDerivative point.2
          (cylinderDigits word length (fun index => coordinate (point.1 index)))) := by
    have digit_continuous : Continuous (fun digits : ℕ → Bool × Bool =>
        cylinderDigits word length (fun index => coordinate (digits index))) :=
      (continuous_cylinderDigits word length).comp
        (continuous_pi (fun index => continuous_coordinate.comp (continuous_apply index)))
    constructor
    · have continuous_full := address_continuous.comp
        (continuous_snd.prodMk (digit_continuous.comp continuous_fst))
      convert continuous_full using 1
      funext point
      exact (cylinder_address (lower_nonnegative.trans point.2.property.1)
        (point.2.property.2.trans_lt upper_lt_one) word length
        (fun index => coordinate (point.1 index))).symm
    · exact derivative_continuous.comp
        (continuous_snd.prodMk (digit_continuous.comp continuous_fst))
  have left_continuous := coordinate_continuous data.leftWord data.leftLength Prod.fst continuous_fst
  have right_continuous := coordinate_continuous data.rightWord data.rightLength Prod.snd continuous_snd
  have power_nonnegative : 0 ≤ exponent - 1 := by linarith [data.exponent_gt_one]
  have formula_continuous :=
    ((left_continuous.2.mul (continuous_const (y := exponent))).mul
      (left_continuous.1.rpow_const (fun _ => Or.inr power_nonnegative))).add
    ((right_continuous.2.mul (continuous_const (y := exponent))).mul
      (right_continuous.1.rpow_const (fun _ => Or.inr power_nonnegative)))
  convert formula_continuous using 1
  funext point
  exact (hasDerivAt_cylinderResidual
    (show 0 < (point.2 : ℝ) by linarith [data.lower_gt_quarter, point.2.property.1])
    (point.2.property.2.trans_lt upper_lt_one) data.exponent_gt_one.le
    data.leftWord data.rightWord data.leftLength data.rightLength point.1).deriv

end LambdaCantor.First.Roots

