import LambdaCantor.Integer.FixedSignedLog
import Mathlib.Tactic.FieldSimp

namespace LambdaCantor.RationalPowers
open Integer

/-- Signed integer multiplication of an outward logarithm enclosure. -/
def scaleSignedInterval (coefficient : ℤ) (bounds : IntInterval) : IntInterval :=
  if 0 ≤ coefficient then ⟨coefficient*bounds.lower,coefficient*bounds.upper⟩
  else ⟨coefficient*bounds.upper,coefficient*bounds.lower⟩

theorem scaleSignedInterval_sound {scale : ℕ} (coefficient : ℤ) (bounds : IntInterval)
    (value : ℝ) (enclosed : bounds.Encloses scale value) :
    (scaleSignedInterval coefficient bounds).Encloses scale ((coefficient : ℝ)*value) := by
  by_cases nonnegative : 0 ≤ coefficient
  · have coefficient_nonnegative : (0 : ℝ) ≤ coefficient := by exact_mod_cast nonnegative
    have lower := mul_le_mul_of_nonneg_left enclosed.1 coefficient_nonnegative
    have upper := mul_le_mul_of_nonneg_left enclosed.2 coefficient_nonnegative
    simp only [scaleSignedInterval, nonnegative, if_true, IntInterval.Encloses, Int.cast_mul]
    constructor <;> nlinarith [lower, upper]
  · have coefficient_nonpositive : (coefficient : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge nonnegative)
    have lower := mul_le_mul_of_nonpos_left enclosed.2 coefficient_nonpositive
    have upper := mul_le_mul_of_nonpos_left enclosed.1 coefficient_nonpositive
    simp only [scaleSignedInterval, nonnegative, if_false, IntInterval.Encloses, Int.cast_mul]
    constructor <;> nlinarith [lower, upper]

/-- Fixed-point arithmetic for the negative rational-exponent corner.
Its integer predicate has size proportional to the fixed lattice precision,
independent of the size of P^a. -/
theorem negative_rational_log_corner {scale numerator denominator : ℕ} (phase : ℤ)
    (scale_positive : 0 < scale) (denominator_positive : 0 < denominator)
    (u v exponentLog : ℝ) (phaseBounds uBounds vBounds exponentBounds : IntInterval)
    (phase_enclosed : phaseBounds.Encloses scale ((phase : ℝ)*Real.log 3))
    (u_enclosed : uBounds.Encloses scale (Real.log u))
    (v_enclosed : vBounds.Encloses scale (Real.log v))
    (exponent_enclosed : exponentBounds.Encloses scale exponentLog)
    (checked : phaseBounds.upper+(numerator : ℤ)*uBounds.upper-
      (denominator : ℤ)*exponentBounds.lower-(denominator : ℤ)*vBounds.lower < 0) :
    ((phase : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log u-exponentLog-Real.log v < 0 := by
  have scale_real_positive : (0 : ℝ) < scale := by exact_mod_cast scale_positive
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  have checked_real : (phaseBounds.upper : ℝ)+(numerator : ℝ)*uBounds.upper-
      (denominator : ℝ)*exponentBounds.lower-(denominator : ℝ)*vBounds.lower < 0 := by
    exact_mod_cast checked
  have u_bound := mul_le_mul_of_nonneg_left u_enclosed.2 (show (0 : ℝ) ≤ numerator by positivity)
  have v_bound := mul_le_mul_of_nonneg_left v_enclosed.1 denominator_real_positive.le
  have exponent_bound := mul_le_mul_of_nonneg_left exponent_enclosed.1 denominator_real_positive.le
  have scaled : (scale : ℝ)*((phase : ℝ)*Real.log 3+
      numerator*Real.log u-denominator*exponentLog-denominator*Real.log v) < 0 := by
    nlinarith [phase_enclosed.2, u_bound, v_bound, exponent_bound]
  have unscaled : (phase : ℝ)*Real.log 3+
      numerator*Real.log u-denominator*exponentLog-denominator*Real.log v < 0 :=
    (mul_lt_mul_iff_right₀ scale_real_positive).mp (by simpa using scaled)
  apply (mul_lt_mul_iff_right₀ denominator_real_positive).mp
  have identity :
      (denominator : ℝ)*(((phase : ℝ)/denominator)*Real.log 3+
        ((numerator : ℝ)/denominator)*Real.log u-exponentLog-Real.log v) =
      (phase : ℝ)*Real.log 3+numerator*Real.log u-
        denominator*exponentLog-denominator*Real.log v := by
    field_simp [denominator_real_positive.ne']
    <;> ring
  rw [identity, mul_zero]
  exact unscaled

theorem positive_rational_log_corner {scale numerator denominator : ℕ} (phase : ℤ)
    (scale_positive : 0 < scale) (denominator_positive : 0 < denominator)
    (u v exponentLog : ℝ) (phaseBounds uBounds vBounds exponentBounds : IntInterval)
    (phase_enclosed : phaseBounds.Encloses scale ((phase : ℝ)*Real.log 3))
    (u_enclosed : uBounds.Encloses scale (Real.log u))
    (v_enclosed : vBounds.Encloses scale (Real.log v))
    (exponent_enclosed : exponentBounds.Encloses scale exponentLog)
    (checked : 0 < phaseBounds.lower+(numerator : ℤ)*uBounds.lower-
      (denominator : ℤ)*exponentBounds.upper-(denominator : ℤ)*vBounds.upper) :
    0 < ((phase : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log u-exponentLog-Real.log v := by
  have scale_real_positive : (0 : ℝ) < scale := by exact_mod_cast scale_positive
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  have checked_real : (0 : ℝ) < (phaseBounds.lower : ℝ)+(numerator : ℝ)*uBounds.lower-
      (denominator : ℝ)*exponentBounds.upper-(denominator : ℝ)*vBounds.upper := by
    exact_mod_cast checked
  have u_bound := mul_le_mul_of_nonneg_left u_enclosed.1 (show (0 : ℝ) ≤ numerator by positivity)
  have v_bound := mul_le_mul_of_nonneg_left v_enclosed.2 denominator_real_positive.le
  have exponent_bound := mul_le_mul_of_nonneg_left exponent_enclosed.2 denominator_real_positive.le
  have scaled : 0 < (scale : ℝ)*((phase : ℝ)*Real.log 3+
      numerator*Real.log u-denominator*exponentLog-denominator*Real.log v) := by
    nlinarith [phase_enclosed.1, u_bound, v_bound, exponent_bound]
  have unscaled : 0 < (phase : ℝ)*Real.log 3+
      numerator*Real.log u-denominator*exponentLog-denominator*Real.log v :=
    (mul_pos_iff_of_pos_left scale_real_positive).mp scaled
  apply (mul_lt_mul_iff_right₀ denominator_real_positive).mp
  have identity :
      (denominator : ℝ)*(((phase : ℝ)/denominator)*Real.log 3+
        ((numerator : ℝ)/denominator)*Real.log u-exponentLog-Real.log v) =
      (phase : ℝ)*Real.log 3+numerator*Real.log u-
        denominator*exponentLog-denominator*Real.log v := by
    field_simp [denominator_real_positive.ne']
    <;> ring
  rw [identity, mul_zero]
  exact unscaled

end LambdaCantor.RationalPowers

