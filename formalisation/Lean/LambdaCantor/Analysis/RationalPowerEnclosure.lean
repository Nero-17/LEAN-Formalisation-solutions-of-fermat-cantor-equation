import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum

/-!
# Exact rational enclosures for rational real powers

The checks below use only natural and integer powers of rational numbers.
Their soundness is a kernel proof, independent of how a particular Boolean
check is evaluated. Ordered nonnegative endpoints are essential: an even
power bound with a negative upper endpoint would not bound the positive root.
-/

namespace LambdaCantor.Analysis

/-- A computable closed enclosure certificate. The integer exponent uses
`zpow` in `ℚ`; no real-power computation occurs in this predicate. -/
def rationalPowerEnclosureCheck (base : ℚ) (numerator : ℤ) (denominator : ℕ)
    (lower upper : ℚ) : Bool :=
  decide (0 < denominator ∧ 0 < base ∧ 0 ≤ lower ∧ lower ≤ upper ∧
    lower ^ denominator ≤ base ^ numerator ∧ base ^ numerator ≤ upper ^ denominator)

/-- The corresponding computable strict enclosure certificate. -/
def rationalPowerStrictEnclosureCheck (base : ℚ) (numerator : ℤ) (denominator : ℕ)
    (lower upper : ℚ) : Bool :=
  decide (0 < denominator ∧ 0 < base ∧ 0 ≤ lower ∧ lower ≤ upper ∧
    lower ^ denominator < base ^ numerator ∧ base ^ numerator < upper ^ denominator)

/-- Raising the positive rational-power root to its denominator recovers the
integer power. This also covers negative integer numerators. -/
theorem rpow_int_div_nat_pow (base : ℝ) (numerator : ℤ) (denominator : ℕ)
    (base_positive : 0 < base) (denominator_nonzero : denominator ≠ 0) :
    (base ^ ((numerator : ℝ) / (denominator : ℝ))) ^ denominator = base ^ numerator := by
  have denominator_cast_nonzero : (denominator : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr denominator_nonzero
  calc
    (base ^ ((numerator : ℝ) / (denominator : ℝ))) ^ denominator =
        (base ^ ((numerator : ℝ) / (denominator : ℝ))) ^ (denominator : ℝ) :=
      (Real.rpow_natCast _ denominator).symm
    _ = base ^ (((numerator : ℝ) / (denominator : ℝ)) * (denominator : ℝ)) :=
      (Real.rpow_mul base_positive.le _ _).symm
    _ = base ^ (numerator : ℝ) := by rw [div_mul_cancel₀ _ denominator_cast_nonzero]
    _ = base ^ numerator := Real.rpow_intCast base numerator

/-- The nonnegative root of the integer-power equation is unique. -/
theorem rpow_int_div_nat_eq_of_nonneg_pow (base : ℝ) (numerator : ℤ) (denominator : ℕ)
    (base_positive : 0 < base) (denominator_nonzero : denominator ≠ 0)
    {root : ℝ} (root_nonnegative : 0 ≤ root)
    (root_equation : root ^ denominator = base ^ numerator) :
    root = base ^ ((numerator : ℝ) / (denominator : ℝ)) := by
  apply (pow_left_inj₀ root_nonnegative
    (Real.rpow_nonneg base_positive.le _) denominator_nonzero).mp
  exact root_equation.trans (rpow_int_div_nat_pow base numerator denominator
    base_positive denominator_nonzero).symm

theorem rationalPowerEnclosure_of_power_bounds
    {base lower upper : ℚ} {numerator : ℤ} {denominator : ℕ}
    (denominator_positive : 0 < denominator) (base_positive : 0 < base)
    (lower_nonnegative : 0 ≤ lower) (endpoints_ordered : lower ≤ upper)
    (lower_power : lower ^ denominator ≤ base ^ numerator)
    (upper_power : base ^ numerator ≤ upper ^ denominator) :
    (lower : ℝ) ≤ (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) ∧
      (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) ≤ (upper : ℝ) := by
  have base_cast_positive : (0 : ℝ) < base := by exact_mod_cast base_positive
  have lower_cast_nonnegative : (0 : ℝ) ≤ lower := by exact_mod_cast lower_nonnegative
  have upper_cast_nonnegative : (0 : ℝ) ≤ upper := by
    exact_mod_cast lower_nonnegative.trans endpoints_ordered
  have lower_cast_power : (lower : ℝ) ^ denominator ≤ (base : ℝ) ^ numerator := by
    exact_mod_cast lower_power
  have upper_cast_power : (base : ℝ) ^ numerator ≤ (upper : ℝ) ^ denominator := by
    exact_mod_cast upper_power
  have root_power := rpow_int_div_nat_pow (base : ℝ) numerator denominator
    base_cast_positive (Nat.ne_of_gt denominator_positive)
  have root_nonnegative := Real.rpow_nonneg base_cast_positive.le
    ((numerator : ℝ) / (denominator : ℝ))
  constructor
  · apply (pow_le_pow_iff_left₀ lower_cast_nonnegative root_nonnegative
      (Nat.ne_of_gt denominator_positive)).mp
    rw [root_power]
    exact lower_cast_power
  · apply (pow_le_pow_iff_left₀ root_nonnegative upper_cast_nonnegative
      (Nat.ne_of_gt denominator_positive)).mp
    rw [root_power]
    exact upper_cast_power

/-- Every successful finite rational certificate encloses the actual real
power. Evaluating the Boolean by `decide` or `native_decide` does not change
this kernel soundness theorem. -/
theorem rationalPowerEnclosureCheck_sound
    {base lower upper : ℚ} {numerator : ℤ} {denominator : ℕ}
    (checked : rationalPowerEnclosureCheck base numerator denominator lower upper = true) :
    (lower : ℝ) ≤ (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) ∧
      (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) ≤ (upper : ℝ) := by
  have conditions : 0 < denominator ∧ 0 < base ∧ 0 ≤ lower ∧ lower ≤ upper ∧
      lower ^ denominator ≤ base ^ numerator ∧ base ^ numerator ≤ upper ^ denominator := by
    simpa only [rationalPowerEnclosureCheck, decide_eq_true_eq] using checked
  exact rationalPowerEnclosure_of_power_bounds conditions.1 conditions.2.1 conditions.2.2.1
    conditions.2.2.2.1 conditions.2.2.2.2.1 conditions.2.2.2.2.2

theorem rationalPowerStrictEnclosure_of_power_bounds
    {base lower upper : ℚ} {numerator : ℤ} {denominator : ℕ}
    (denominator_positive : 0 < denominator) (base_positive : 0 < base)
    (lower_nonnegative : 0 ≤ lower) (endpoints_ordered : lower ≤ upper)
    (lower_power : lower ^ denominator < base ^ numerator)
    (upper_power : base ^ numerator < upper ^ denominator) :
    (lower : ℝ) < (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) ∧
      (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) < (upper : ℝ) := by
  have base_cast_positive : (0 : ℝ) < base := by exact_mod_cast base_positive
  have lower_cast_nonnegative : (0 : ℝ) ≤ lower := by exact_mod_cast lower_nonnegative
  have upper_cast_nonnegative : (0 : ℝ) ≤ upper := by
    exact_mod_cast lower_nonnegative.trans endpoints_ordered
  have lower_cast_power : (lower : ℝ) ^ denominator < (base : ℝ) ^ numerator := by
    exact_mod_cast lower_power
  have upper_cast_power : (base : ℝ) ^ numerator < (upper : ℝ) ^ denominator := by
    exact_mod_cast upper_power
  have root_power := rpow_int_div_nat_pow (base : ℝ) numerator denominator
    base_cast_positive (Nat.ne_of_gt denominator_positive)
  have root_nonnegative := Real.rpow_nonneg base_cast_positive.le
    ((numerator : ℝ) / (denominator : ℝ))
  constructor
  · apply (pow_lt_pow_iff_left₀ lower_cast_nonnegative root_nonnegative
      (Nat.ne_of_gt denominator_positive)).mp
    rw [root_power]
    exact lower_cast_power
  · apply (pow_lt_pow_iff_left₀ root_nonnegative upper_cast_nonnegative
      (Nat.ne_of_gt denominator_positive)).mp
    rw [root_power]
    exact upper_cast_power

theorem rationalPowerStrictEnclosureCheck_sound
    {base lower upper : ℚ} {numerator : ℤ} {denominator : ℕ}
    (checked : rationalPowerStrictEnclosureCheck base numerator denominator lower upper = true) :
    (lower : ℝ) < (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) ∧
      (base : ℝ) ^ ((numerator : ℝ) / (denominator : ℝ)) < (upper : ℝ) := by
  have conditions : 0 < denominator ∧ 0 < base ∧ 0 ≤ lower ∧ lower ≤ upper ∧
      lower ^ denominator < base ^ numerator ∧ base ^ numerator < upper ^ denominator := by
    simpa only [rationalPowerStrictEnclosureCheck, decide_eq_true_eq] using checked
  exact rationalPowerStrictEnclosure_of_power_bounds conditions.1 conditions.2.1 conditions.2.2.1
    conditions.2.2.2.1 conditions.2.2.2.2.1 conditions.2.2.2.2.2

end LambdaCantor.Analysis
