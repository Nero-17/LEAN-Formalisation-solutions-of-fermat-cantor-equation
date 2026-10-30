import LambdaCantor.RationalPowers.ExceptionalSource
import LambdaCantor.Analysis.RealPowerBoxError
import Mathlib.Tactic.Push

noncomputable section
namespace LambdaCantor.RationalPowers.Exceptional

theorem PowerSource.shifted_exponent (source : PowerSource)
    (denominator_positive : 0 < source.denominator) (shift : ℤ) :
    (((source.numerator-shift*source.denominator : ℤ) : ℝ)/(source.denominator : ℝ)) =
      (source.exponent : ℝ)-(shift : ℝ) := by
  have denominator_nonzero : (source.denominator : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt denominator_positive
  unfold PowerSource.exponent
  push_cast
  field_simp [denominator_nonzero]
  <;> ring

theorem PowerSource.shifted_bounds (source : PowerSource)
    (denominator_positive : 0 < source.denominator) (shift : ℤ)
    (base : ℚ) (bounds : PowerBounds)
    (checked : bounds.check base (source.numerator-shift*source.denominator) source.denominator = true) :
    (bounds.lower : ℝ) ≤ (base : ℝ)^((source.exponent : ℝ)-(shift : ℝ)) ∧
      (base : ℝ)^((source.exponent : ℝ)-(shift : ℝ)) ≤ (bounds.upper : ℝ) := by
  have result := PowerBounds.sound checked
  rw [source.shifted_exponent denominator_positive shift] at result
  exact result

structure PowerSource.RealBounds (source : PowerSource) : Prop where
  horizontalValue : (source.horizontalValue.lower : ℝ) ≤
      (source.horizontalBase : ℝ)^(source.exponent : ℝ) ∧
      (source.horizontalBase : ℝ)^(source.exponent : ℝ) ≤ source.horizontalValue.upper
  verticalValue : (source.verticalValue.lower : ℝ) ≤
      (source.verticalBase : ℝ)^(source.exponent : ℝ) ∧
      (source.verticalBase : ℝ)^(source.exponent : ℝ) ≤ source.verticalValue.upper
  horizontalDerivative : (source.horizontalDerivative.lower : ℝ) ≤
      (source.horizontalBase : ℝ)^((source.exponent : ℝ)-1) ∧
      (source.horizontalBase : ℝ)^((source.exponent : ℝ)-1) ≤ source.horizontalDerivative.upper
  verticalDerivative : (source.verticalDerivative.lower : ℝ) ≤
      (source.verticalBase : ℝ)^((source.exponent : ℝ)-1) ∧
      (source.verticalBase : ℝ)^((source.exponent : ℝ)-1) ≤ source.verticalDerivative.upper
  horizontalSecond : (source.horizontalBase : ℝ)^((source.exponent : ℝ)-2) ≤ source.horizontalSecond.upper
  horizontalSecondUpper : ((source.horizontalBase : ℝ)+(source.horizontalScale : ℝ))^
      ((source.exponent : ℝ)-2) ≤ source.horizontalSecondUpper.upper
  verticalSecond : (source.verticalBase : ℝ)^((source.exponent : ℝ)-2) ≤ source.verticalSecond.upper
  verticalSecondUpper : ((source.verticalBase : ℝ)+(source.verticalScale : ℝ))^
      ((source.exponent : ℝ)-2) ≤ source.verticalSecondUpper.upper

theorem PowerSource.realBounds (source : PowerSource) (valid : source.Valid) : source.RealBounds := by
  have denominator_positive := valid.1.1
  obtain ⟨horizontalValue,verticalValue,horizontalDerivative,verticalDerivative,
    horizontalSecond,horizontalSecondUpper,verticalSecond,verticalSecondUpper⟩ := valid.2.1
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using source.shifted_bounds denominator_positive 0 source.horizontalBase
      source.horizontalValue (by simpa using horizontalValue)
  · simpa using source.shifted_bounds denominator_positive 0 source.verticalBase
      source.verticalValue (by simpa using verticalValue)
  · simpa using source.shifted_bounds denominator_positive 1 source.horizontalBase
      source.horizontalDerivative (by simpa using horizontalDerivative)
  · simpa using source.shifted_bounds denominator_positive 1 source.verticalBase
      source.verticalDerivative (by simpa using verticalDerivative)
  · simpa using (source.shifted_bounds denominator_positive 2 source.horizontalBase
      source.horizontalSecond (by simpa using horizontalSecond)).2
  · simpa only [Rat.cast_add, Int.cast_ofNat, Nat.cast_ofNat] using
      (source.shifted_bounds denominator_positive 2 (source.horizontalBase+source.horizontalScale)
        source.horizontalSecondUpper (by simpa using horizontalSecondUpper)).2
  · simpa using (source.shifted_bounds denominator_positive 2 source.verticalBase
      source.verticalSecond (by simpa using verticalSecond)).2
  · simpa only [Rat.cast_add, Int.cast_ofNat, Nat.cast_ofNat] using
      (source.shifted_bounds denominator_positive 2 (source.verticalBase+source.verticalScale)
        source.verticalSecondUpper (by simpa using verticalSecondUpper)).2

theorem PowerSource.real_geometry (source : PowerSource) (valid : source.Valid) :
    1 < (source.exponent : ℝ) ∧ 0 < (source.horizontalBase : ℝ) ∧
    0 < (source.verticalBase : ℝ) ∧ 0 < (source.horizontalScale : ℝ) ∧
    0 < (source.verticalScale : ℝ) ∧ 0 < (source.normalization : ℝ) := by
  obtain ⟨_,exponent,horizontal,vertical,_,_,_,_,_,_,normalization,_⟩ := valid.1
  have horizontal_scale : 0 < source.horizontalScale := by
    unfold PowerSource.horizontalScale
    positivity
  have vertical_scale : 0 < source.verticalScale := by
    unfold PowerSource.verticalScale
    positivity
  have horizontal_base : 0 < source.horizontalBase :=
    mul_pos (Nat.cast_pos.mpr horizontal) horizontal_scale
  have vertical_base : 0 < source.verticalBase :=
    mul_pos (Nat.cast_pos.mpr vertical) vertical_scale
  exact ⟨by exact_mod_cast exponent, by exact_mod_cast horizontal_base,
    by exact_mod_cast vertical_base, by exact_mod_cast horizontal_scale,
    by exact_mod_cast vertical_scale, by exact_mod_cast normalization⟩

private theorem abs_sub_le_of_endpoint_bounds {value lower upper reference bound : ℝ}
    (lower_bound : lower ≤ value) (upper_bound : value ≤ upper)
    (lower_error : |lower-reference| ≤ bound) (upper_error : |upper-reference| ≤ bound) :
    |value-reference| ≤ bound := by
  rw [abs_le] at lower_error upper_error ⊢
  constructor <;> linarith [lower_error.1,upper_error.2]

theorem PowerSource.coefficient_errors (source : PowerSource) (valid : source.Valid) :
    |(source.exponent : ℝ)*(source.horizontalBase : ℝ)^((source.exponent : ℝ)-1)*
        source.horizontalScale/source.normalization-(source.slope : ℝ)/2| ≤
      (source.horizontalCoefficientError : ℝ) ∧
    |(source.exponent : ℝ)*(source.verticalBase : ℝ)^((source.exponent : ℝ)-1)*
        source.verticalScale/source.normalization-1/2| ≤ (source.verticalCoefficientError : ℝ) := by
  have geometry := source.real_geometry valid
  have bounds := source.realBounds valid
  obtain ⟨_,_,horizontalLower,horizontalUpper,verticalLower,verticalUpper,_,_⟩ := valid.2.2.1
  have exponent_positive : 0 < (source.exponent : ℝ) := by linarith [geometry.1]
  have horizontal_factor : 0 ≤ (source.exponent : ℝ)*source.horizontalScale/source.normalization :=
    (div_pos (mul_pos exponent_positive geometry.2.2.2.1) geometry.2.2.2.2.2).le
  have vertical_factor : 0 ≤ (source.exponent : ℝ)*source.verticalScale/source.normalization :=
    (div_pos (mul_pos exponent_positive geometry.2.2.2.2.1) geometry.2.2.2.2.2).le
  constructor
  · apply abs_sub_le_of_endpoint_bounds
      (lower := ((source.exponent*source.horizontalDerivative.lower*source.horizontalScale/source.normalization : ℚ) : ℝ))
      (upper := ((source.exponent*source.horizontalDerivative.upper*source.horizontalScale/source.normalization : ℚ) : ℝ))
    · push_cast
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left bounds.horizontalDerivative.1 horizontal_factor
    · push_cast
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left bounds.horizontalDerivative.2 horizontal_factor
    · exact_mod_cast horizontalLower
    · exact_mod_cast horizontalUpper
  · apply abs_sub_le_of_endpoint_bounds
      (lower := ((source.exponent*source.verticalDerivative.lower*source.verticalScale/source.normalization : ℚ) : ℝ))
      (upper := ((source.exponent*source.verticalDerivative.upper*source.verticalScale/source.normalization : ℚ) : ℝ))
    · push_cast
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left bounds.verticalDerivative.1 vertical_factor
    · push_cast
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left bounds.verticalDerivative.2 vertical_factor
    · simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
        Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr verticalLower
    · simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
        Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr verticalUpper

theorem PowerSource.reference_error_bound (source : PowerSource) (valid : source.Valid) :
    Analysis.realPowerBoxReferenceErrorBound source.exponent source.horizontalBase source.verticalBase
      source.horizontalScale source.verticalScale source.normalization source.slope ≤ (source.error : ℝ) := by
  have geometry := source.real_geometry valid
  have bounds := source.realBounds valid
  have coefficients := source.coefficient_errors valid
  have exponent_positive : 0 ≤ (source.exponent : ℝ) := by linarith [geometry.1]
  have horizontal_second :
      Analysis.realPowerSecondBound source.exponent source.horizontalBase source.horizontalScale ≤
      ((source.exponent * |source.exponent-1| *
        max source.horizontalSecond.upper source.horizontalSecondUpper.upper : ℚ) : ℝ) := by
    unfold Analysis.realPowerSecondBound
    push_cast
    apply mul_le_mul_of_nonneg_left (max_le_max bounds.horizontalSecond bounds.horizontalSecondUpper)
      (mul_nonneg exponent_positive (abs_nonneg _))
  have vertical_second :
      Analysis.realPowerSecondBound source.exponent source.verticalBase source.verticalScale ≤
      ((source.exponent * |source.exponent-1| *
        max source.verticalSecond.upper source.verticalSecondUpper.upper : ℚ) : ℝ) := by
    unfold Analysis.realPowerSecondBound
    push_cast
    apply mul_le_mul_of_nonneg_left (max_le_max bounds.verticalSecond bounds.verticalSecondUpper)
      (mul_nonneg exponent_positive (abs_nonneg _))
  have second_error :
      Analysis.realPowerBoxErrorBound source.exponent source.horizontalBase source.verticalBase
        source.horizontalScale source.verticalScale source.normalization ≤
      (((source.horizontalScale^2 * (source.exponent * |source.exponent-1| *
          max source.horizontalSecond.upper source.horizontalSecondUpper.upper) +
        source.verticalScale^2 * (source.exponent * |source.exponent-1| *
          max source.verticalSecond.upper source.verticalSecondUpper.upper)) / source.normalization : ℚ) : ℝ) := by
    unfold Analysis.realPowerBoxErrorBound
    push_cast at horizontal_second vertical_second
    push_cast
    apply div_le_div_of_nonneg_right _ geometry.2.2.2.2.2.le
    exact add_le_add
      (mul_le_mul_of_nonneg_left horizontal_second (sq_nonneg _))
      (mul_le_mul_of_nonneg_left vertical_second (sq_nonneg _))
  unfold Analysis.realPowerBoxReferenceErrorBound PowerSource.error
  push_cast at second_error ⊢
  linarith [coefficients.1,coefficients.2]

end LambdaCantor.RationalPowers.Exceptional
