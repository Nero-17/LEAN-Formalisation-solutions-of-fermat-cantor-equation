import LambdaCantor.Integer.FixedLogArithmetic

namespace LambdaCantor.Integer

structure IntInterval where
  lower : ℤ
  upper : ℤ
  deriving DecidableEq, Inhabited

def IntInterval.Encloses (scale : ℕ) (bounds : IntInterval) (value : ℝ) : Prop :=
  (bounds.lower : ℝ) ≤ (scale : ℝ)*value ∧ (scale : ℝ)*value ≤ bounds.upper

def signedLogInterval (scale numerator denominator terms : ℕ) : IntInterval :=
  if denominator ≤ numerator then
    let result := logUnitInterval scale numerator denominator terms
    ⟨result.lower,result.upper⟩
  else
    let result := logUnitInterval scale denominator numerator terms
    ⟨-(result.upper : ℤ),-(result.lower : ℤ)⟩

def signedLogStrict (scale numerator denominator : ℕ) : Prop :=
  if denominator ≤ numerator then (logParameter scale numerator denominator).upper < scale
  else (logParameter scale denominator numerator).upper < scale

instance (scale numerator denominator : ℕ) : Decidable (signedLogStrict scale numerator denominator) := by
  unfold signedLogStrict
  infer_instance

theorem signedLogInterval_sound (scale numerator denominator terms : ℕ)
    (scalePositive : 0 < scale) (numeratorPositive : 0 < numerator)
    (denominatorPositive : 0 < denominator)
    (strict : signedLogStrict scale numerator denominator) :
    (signedLogInterval scale numerator denominator terms).Encloses scale
      (Real.log ((numerator : ℝ)/denominator)) := by
  by_cases ordered : denominator ≤ numerator
  · simp only [signedLogStrict,ordered,if_true] at strict
    have enclosed := logUnitInterval_sound scale numerator denominator terms scalePositive
      denominatorPositive ordered strict
    simpa only [signedLogInterval,ordered,if_true,IntInterval.Encloses,NatInterval.Encloses,Int.cast_natCast]
      using enclosed
  · simp only [signedLogStrict,ordered,if_false] at strict
    have enclosed := logUnitInterval_sound scale denominator numerator terms scalePositive
      numeratorPositive (by omega) strict
    have numeratorNonzero : (numerator : ℝ) ≠ 0 := by positivity
    have denominatorNonzero : (denominator : ℝ) ≠ 0 := by positivity
    have identity : Real.log ((numerator : ℝ)/denominator) =
        -Real.log ((denominator : ℝ)/numerator) := by
      rw [Real.log_div numeratorNonzero denominatorNonzero,
        Real.log_div denominatorNonzero numeratorNonzero]
      ring
    simp only [signedLogInterval,ordered,if_false,IntInterval.Encloses,
      Int.cast_neg,Int.cast_natCast,identity]
    constructor <;> nlinarith [enclosed.1,enclosed.2]

/-- Four integer endpoint products certify division by a positive interval.
This intentionally avoids sign branches in the certificate format. -/
theorem fixed_division_bounds (scale : ℕ) (scalePositive : 0 < scale)
    (numerator denominator : ℝ) (denominatorPositive : 0 < denominator)
    (numeratorBounds denominatorBounds : IntInterval)
    (numeratorEnclosed : numeratorBounds.Encloses scale numerator)
    (denominatorEnclosed : denominatorBounds.Encloses scale denominator)
    (lower upper : ℤ)
    (lowerFirst : lower*denominatorBounds.lower ≤ numeratorBounds.lower)
    (lowerSecond : lower*denominatorBounds.upper ≤ numeratorBounds.lower)
    (upperFirst : numeratorBounds.upper ≤ upper*denominatorBounds.lower)
    (upperSecond : numeratorBounds.upper ≤ upper*denominatorBounds.upper) :
    (lower : ℝ) ≤ numerator/denominator ∧ numerator/denominator ≤ upper := by
  have scaleRealPositive : (0 : ℝ) < scale := by exact_mod_cast scalePositive
  have lowerFirstReal : (lower : ℝ)*denominatorBounds.lower ≤ numeratorBounds.lower := by
    exact_mod_cast lowerFirst
  have lowerSecondReal : (lower : ℝ)*denominatorBounds.upper ≤ numeratorBounds.lower := by
    exact_mod_cast lowerSecond
  have upperFirstReal : (numeratorBounds.upper : ℝ) ≤ (upper : ℝ)*denominatorBounds.lower := by
    exact_mod_cast upperFirst
  have upperSecondReal : (numeratorBounds.upper : ℝ) ≤ (upper : ℝ)*denominatorBounds.upper := by
    exact_mod_cast upperSecond
  constructor
  · apply (le_div_iff₀ denominatorPositive).2
    apply le_of_mul_le_mul_left (a := (scale : ℝ)) _ scaleRealPositive
    by_cases sign : 0 ≤ (lower : ℝ)
    · have product := mul_le_mul_of_nonneg_left denominatorEnclosed.2 sign
      nlinarith [numeratorEnclosed.1,product]
    · have product := mul_le_mul_of_nonpos_left denominatorEnclosed.1 (le_of_not_ge sign)
      nlinarith [numeratorEnclosed.1,product]
  · apply (div_le_iff₀ denominatorPositive).2
    apply le_of_mul_le_mul_left (a := (scale : ℝ)) _ scaleRealPositive
    by_cases sign : 0 ≤ (upper : ℝ)
    · have product := mul_le_mul_of_nonneg_left denominatorEnclosed.1 sign
      nlinarith [numeratorEnclosed.2,product]
    · have product := mul_le_mul_of_nonpos_left denominatorEnclosed.2 (le_of_not_ge sign)
      nlinarith [numeratorEnclosed.2,product]

end LambdaCantor.Integer
