import LambdaCantor.Integer.FixedLog

namespace LambdaCantor.Integer

def NatInterval.scaleBy (bounds : NatInterval) (coefficient : ℕ) : NatInterval :=
  ⟨coefficient*bounds.lower,coefficient*bounds.upper⟩

theorem NatInterval.scaleBy_sound {scale coefficient : ℕ} {bounds : NatInterval}
    {value : ℝ} (enclosed : bounds.Encloses scale value) :
    (bounds.scaleBy coefficient).Encloses scale ((coefficient : ℝ)*value) := by
  obtain ⟨lower,upper⟩ := enclosed
  have lowerScaled := mul_le_mul_of_nonneg_left lower
    (show (0 : ℝ) ≤ coefficient by positivity)
  have upperScaled := mul_le_mul_of_nonneg_left upper
    (show (0 : ℝ) ≤ coefficient by positivity)
  unfold NatInterval.Encloses NatInterval.scaleBy
  push_cast
  constructor <;> nlinarith

/-- A supplied base-three exponent avoids recursion in the certificate decoder. -/
def logIntegerInterval (scale numerator exponent terms : ℕ) : NatInterval :=
  (logUnitInterval scale numerator (3^exponent) terms).add
    ((logUnitInterval scale 3 1 terms).scaleBy exponent)

theorem logIntegerInterval_sound (scale numerator exponent terms : ℕ)
    (scalePositive : 0 < scale) (ordered : 3^exponent ≤ numerator)
    (strict : (logParameter scale numerator (3^exponent)).upper < scale)
    (threeStrict : (logParameter scale 3 1).upper < scale) :
    (logIntegerInterval scale numerator exponent terms).Encloses scale
      (Real.log numerator) := by
  have denominatorPositive : 0 < (3 : ℕ)^exponent := by positivity
  have numeratorPositive : 0 < numerator := lt_of_lt_of_le denominatorPositive ordered
  have first := logUnitInterval_sound scale numerator (3^exponent) terms
    scalePositive denominatorPositive ordered strict
  have second := logUnitInterval_sound scale 3 1 terms scalePositive (by decide)
    (by decide) threeStrict
  have result := NatInterval.add_sound first (NatInterval.scaleBy_sound
    (coefficient := exponent) second)
  have numeratorNonzero : (numerator : ℝ) ≠ 0 := by positivity
  have denominatorNonzero : ((3^exponent : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Real.log_div numeratorNonzero denominatorNonzero] at result
  simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow,Nat.cast_one,div_one] at result
  simpa only [logIntegerInterval,sub_add_cancel] using result

/-- Only the corner comparison is abstract here. Every interval supplied to
this theorem must separately enclose its stated real logarithm. -/
theorem strict_log_corner_of_intervals {scale n d : ℕ}
    (scalePositive : 0 < scale) {u v : ℝ}
    {logU logV logN logThree : NatInterval}
    (uEnclosed : logU.Encloses scale (Real.log u))
    (vEnclosed : logV.Encloses scale (Real.log v))
    (nEnclosed : logN.Encloses scale (Real.log n))
    (threeEnclosed : logThree.Encloses scale (Real.log 3))
    (checked : (n : ℤ)*logU.lower+logN.lower >
      (logV.upper : ℤ)+(d : ℤ)*logThree.upper) :
    -(n : ℝ)*Real.log u+Real.log v-Real.log n+(d : ℝ)*Real.log 3 < 0 := by
  have scaleRealPositive : (0 : ℝ) < scale := by exact_mod_cast scalePositive
  have checkedReal : (n : ℝ)*logU.lower+logN.lower >
      (logV.upper : ℝ)+(d : ℝ)*logThree.upper := by exact_mod_cast checked
  have uScaled := mul_le_mul_of_nonneg_left uEnclosed.1
    (show (0 : ℝ) ≤ n by positivity)
  have threeScaled := mul_le_mul_of_nonneg_left threeEnclosed.2
    (show (0 : ℝ) ≤ d by positivity)
  have strictScaled : (scale : ℝ)*
      (-(n : ℝ)*Real.log u+Real.log v-Real.log n+(d : ℝ)*Real.log 3) < 0 := by
    nlinarith [vEnclosed.2,nEnclosed.1,uScaled,threeScaled]
  exact (mul_lt_mul_iff_right₀ scaleRealPositive).1 (by simpa using strictScaled)

theorem strict_log_corner_positive_of_intervals {scale n d : ℕ}
    (scalePositive : 0 < scale) {u v : ℝ}
    {logU logV logN logThree : NatInterval}
    (uEnclosed : logU.Encloses scale (Real.log u))
    (vEnclosed : logV.Encloses scale (Real.log v))
    (nEnclosed : logN.Encloses scale (Real.log n))
    (threeEnclosed : logThree.Encloses scale (Real.log 3))
    (checked : (n : ℤ)*logU.upper+logN.upper <
      (logV.lower : ℤ)+(d : ℤ)*logThree.lower) :
    0 < -(n : ℝ)*Real.log u+Real.log v-Real.log n+(d : ℝ)*Real.log 3 := by
  have scaleRealPositive : (0 : ℝ) < scale := by exact_mod_cast scalePositive
  have checkedReal : (n : ℝ)*logU.upper+logN.upper <
      (logV.lower : ℝ)+(d : ℝ)*logThree.lower := by exact_mod_cast checked
  have uScaled := mul_le_mul_of_nonneg_left uEnclosed.2
    (show (0 : ℝ) ≤ n by positivity)
  have threeScaled := mul_le_mul_of_nonneg_left threeEnclosed.1
    (show (0 : ℝ) ≤ d by positivity)
  have strictScaled : 0 < (scale : ℝ)*
      (-(n : ℝ)*Real.log u+Real.log v-Real.log n+(d : ℝ)*Real.log 3) := by
    nlinarith [vEnclosed.1,nEnclosed.2,uScaled,threeScaled]
  exact (mul_pos_iff_of_pos_left scaleRealPositive).1 strictScaled

end LambdaCantor.Integer
