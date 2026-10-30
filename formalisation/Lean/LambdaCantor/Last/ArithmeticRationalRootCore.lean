import LambdaCantor.Last.ArithmeticField
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last
/-- Bézout's identity recovers the positive denominator-th root once the
coordinate and its reduced rational power both belong to the field. -/
theorem denominator_root_mem_subfield (field : Subfield ℝ)
    {coordinate : ℝ} (positive : 0 < coordinate)
    {numerator denominator : ℕ} (denominator_positive : 0 < denominator)
    (coprime : numerator.Coprime denominator)
    (coordinate_mem : coordinate ∈ field)
    (power_mem : coordinate ^ ((numerator : ℝ)/denominator) ∈ field) :
    coordinate ^ (1/(denominator : ℝ)) ∈ field := by
  have bezout : (numerator : ℤ)*Nat.gcdA numerator denominator +
      (denominator : ℤ)*Nat.gcdB numerator denominator = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, coprime.gcd_eq_one]
    norm_num
  have bezout_real : (numerator : ℝ)*(Nat.gcdA numerator denominator : ℝ) +
      (denominator : ℝ)*(Nat.gcdB numerator denominator : ℝ) = 1 := by
    exact_mod_cast bezout
  have denominator_nonzero : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast denominator_positive.ne'
  have exponent_eq : (1 : ℝ)/denominator =
      ((numerator : ℝ)/denominator)*(Nat.gcdA numerator denominator : ℝ) +
        (Nat.gcdB numerator denominator : ℝ) := by
    apply (div_eq_iff denominator_nonzero).mpr
    field_simp
    nlinarith
  rw [exponent_eq, Real.rpow_add positive,
    Real.rpow_mul positive.le, Real.rpow_intCast, Real.rpow_intCast]
  exact field.mul_mem (field.zpow_mem power_mem _) (field.zpow_mem coordinate_mem _)

theorem denominator_root_pow_numerator {coordinate : ℝ} (positive : 0 < coordinate)
    (numerator denominator : ℕ) :
    (coordinate ^ (1/(denominator : ℝ))) ^ numerator =
      coordinate ^ ((numerator : ℝ)/denominator) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul positive.le]
  congr 1
  ring


end LambdaCantor.Last

