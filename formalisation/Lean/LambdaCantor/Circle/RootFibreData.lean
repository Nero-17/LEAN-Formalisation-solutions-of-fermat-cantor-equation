import LambdaCantor.Circle.RootFibreInterface
import LambdaCantor.First.RootFibreTopology

noncomputable section
namespace LambdaCantor.Circle
open LambdaCantor.First.Roots

theorem onset_gt_quarter : (1 / 4 : ℝ) < onset := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have := Real.sqrt_nonneg (3 : ℝ)
  dsimp [onset]
  nlinarith

theorem circle_cylinderCoordinate_values (depth : ℕ) (ratio : ℝ)
    (firstDigits secondDigits : ℕ → Bool) :
    cylinderCoordinate (circleHorizontalPrefix depth) (3 * depth + 1) firstDigits ratio =
        (1 - ratio) * ratio ^ depth + ratio * (ratio ^ depth) ^ 3 * address ratio firstDigits ∧
    cylinderCoordinate (circleVerticalPrefix depth) (4 * depth + 1) secondDigits ratio =
        1 - ratio * (ratio ^ depth) ^ 2 + ratio * (ratio ^ depth) ^ 4 * address ratio secondDigits := by
  unfold cylinderCoordinate
  rw [circle_horizontal_prefix_value, circle_vertical_prefix_value]
  have twice : ratio ^ (2 * depth) = (ratio ^ depth) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  have thrice : ratio ^ (3 * depth) = (ratio ^ depth) ^ 3 := by rw [Nat.mul_comm, pow_mul]
  have four : ratio ^ (4 * depth) = (ratio ^ depth) ^ 4 := by rw [Nat.mul_comm, pow_mul]
  simp only [pow_succ, twice, thrice, four]
  constructor <;> ring

theorem circle_cylinderResidual_eq (depth : ℕ) (digits : ℕ → Bool × Bool) (ratio : ℝ) :
    cylinderResidual 2 (circleHorizontalPrefix depth) (circleVerticalPrefix depth)
      (3 * depth + 1) (4 * depth + 1) digits ratio =
    ratio ^ (2 * depth) * expandedCircleResidual depth
      (fun parameter => address parameter (fun index => (digits index).1))
      (fun parameter => address parameter (fun index => (digits index).2)) ratio := by
  unfold cylinderResidual
  rw [Real.rpow_two, Real.rpow_two,
    (circle_cylinderCoordinate_values depth ratio (fun index => (digits index).1)
      (fun index => (digits index).2)).1,
    (circle_cylinderCoordinate_values depth ratio (fun index => (digits index).1)
      (fun index => (digits index).2)).2,
    expandedCircleResidual_eq]
  have twice : ratio ^ (2 * depth) = (ratio ^ depth) ^ 2 := by rw [Nat.mul_comm, pow_mul]
  rw [twice]
  exact root_residual_identity ratio (ratio ^ depth) _ _

/-- The root construction supplies every hypothesis of the actual root-fibre
interface, including a uniform bound for the derivative of the unnormalised
cylinder residual. -/
theorem circle_rootFibreData_exists (depth : ℕ) (large : 2 ≤ depth) :
    ∃ data : RootFibreData 2,
      data.root = circleAddressRoot depth large ∧ onset < data.lower ∧
      data.upper < onset + 2 * (7 / 25 : ℝ) ^ (2 * depth + 1) := by
  obtain ⟨lower, upper, lower_above, ordered, upper_near, upper_bound, roots_in_band⟩ :=
    circle_roots_compact_band depth large
  have lower_positive : 0 < lower := onset_pos.trans lower_above
  have band_positive : ∀ ratio ∈ Set.Icc lower upper, 0 < ratio :=
    fun ratio member => lower_positive.trans_le member.1
  have band_less_one : ∀ ratio ∈ Set.Icc lower upper, ratio < 1 :=
    fun ratio member => member.2.trans_lt (upper_bound.trans (by norm_num))
  refine ⟨{
    exponent_gt_one := by norm_num
    lower := lower
    upper := upper
    lower_gt_quarter := onset_gt_quarter.trans lower_above
    upper_lt_half := upper_bound.trans (by norm_num)
    ordered := ordered
    leftWord := circleHorizontalPrefix depth
    rightWord := circleVerticalPrefix depth
    leftLength := 3 * depth + 1
    rightLength := 4 * depth + 1
    root := circleAddressRoot depth large
    root_in_band := roots_in_band
    left_positive := ?_
    right_positive := ?_
    unique_root := ?_
    derivative_lower_bound := lower ^ (2 * depth)
    derivative_lower_bound_positive := pow_pos lower_positive _
    transverse := ?_
  }, rfl, lower_above, upper_near⟩
  · intro digits ratio member
    rw [(circle_cylinderCoordinate_values depth ratio (fun index => (digits index).1)
      (fun index => (digits index).2)).1]
    have positive := band_positive ratio member
    have less_one := band_less_one ratio member
    have tail_nonnegative := (cantorSet_subset_unitInterval positive.le less_one
      (Set.mem_range_self (fun index => (digits index).1))).1
    positivity
  · intro digits ratio member
    rw [(circle_cylinderCoordinate_values depth ratio (fun index => (digits index).1)
      (fun index => (digits index).2)).2]
    have positive := band_positive ratio member
    have less_one := band_less_one ratio member
    have tail_nonnegative := (cantorSet_subset_unitInterval positive.le less_one
      (Set.mem_range_self (fun index => (digits index).2))).1
    have power_small : ratio * (ratio ^ depth) ^ 2 < 1 := by
      have power_bound := power_antitone positive.le less_one.le (show 1 ≤ 2 * depth + 1 by omega)
      have twice : ratio ^ (2 * depth) = (ratio ^ depth) ^ 2 := by rw [Nat.mul_comm, pow_mul]
      rw [pow_succ', twice, pow_one] at power_bound
      exact power_bound.trans_lt less_one
    have tail_term_nonnegative : 0 ≤ ratio * (ratio ^ depth) ^ 4 *
        address ratio (fun index => (digits index).2) := by positivity
    linarith
  · intro digits ratio member
    rw [circle_cylinderResidual_eq]
    have positive := band_positive ratio member
    have root_zero := (circleAddressRoot_spec depth large digits).2
    have strict := circle_address_residual_strictAnti depth large
      (fun index => (digits index).1) (fun index => (digits index).2)
    constructor
    · intro zero
      have normalized_zero := (mul_eq_zero.mp zero).resolve_left (ne_of_gt (pow_pos positive _))
      apply strict.injOn
        ⟨lower_above.le.trans member.1, member.2.trans upper_bound.le⟩
        ⟨(circleAddressRoot_spec depth large digits).1.1.le,
          (circleAddressRoot_spec depth large digits).1.2.le⟩
      exact normalized_zero.trans root_zero.symm
    · rintro rfl
      rw [root_zero, mul_zero]
  · intro digits
    have root_bounds := circleAddressRoot_spec depth large digits
    have root_positive := onset_pos.trans root_bounds.1.1
    obtain ⟨derivative, has_derivative, derivative_negative⟩ :=
      circle_address_residual_transverse depth large _ root_positive root_bounds.1.2.le
        (fun index => (digits index).1) (fun index => (digits index).2)
    have product_derivative := ((hasDerivAt_id (circleAddressRoot depth large digits)).pow
      (2 * depth)).mul has_derivative
    have product_function_eq :
        (id ^ (2 * depth) * expandedCircleResidual depth
          (fun parameter => address parameter (fun index => (digits index).1))
          (fun parameter => address parameter (fun index => (digits index).2))) =
        (fun ratio => ratio ^ (2 * depth) * expandedCircleResidual depth
          (fun parameter => address parameter (fun index => (digits index).1))
          (fun parameter => address parameter (fun index => (digits index).2)) ratio) := by
      funext ratio
      simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    rw [product_function_eq] at product_derivative
    have cylinder_derivative : deriv
        (cylinderResidual 2 (circleHorizontalPrefix depth) (circleVerticalPrefix depth)
          (3 * depth + 1) (4 * depth + 1) digits)
        (circleAddressRoot depth large digits) =
        (circleAddressRoot depth large digits) ^ (2 * depth) * derivative := by
      have function_eq : cylinderResidual 2 (circleHorizontalPrefix depth) (circleVerticalPrefix depth)
          (3 * depth + 1) (4 * depth + 1) digits =
          fun ratio => ratio ^ (2 * depth) * expandedCircleResidual depth
            (fun parameter => address parameter (fun index => (digits index).1))
            (fun parameter => address parameter (fun index => (digits index).2)) ratio := by
        funext ratio
        exact circle_cylinderResidual_eq depth digits ratio
      rw [function_eq]
      simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, root_bounds.2, mul_zero, zero_add]
        using product_derivative.deriv
    rw [cylinder_derivative, abs_mul, abs_of_pos (pow_pos root_positive _), abs_of_neg (by linarith)]
    have power_bound := pow_le_pow_left₀ lower_positive.le (roots_in_band digits).1 (2 * depth)
    have root_power_positive := pow_pos root_positive (2 * depth)
    nlinarith

end LambdaCantor.Circle
