import LambdaCantor.Integer.TailEnclosure

namespace LambdaCantor.Integer

/-- A checked enclosure of the finite endpoint and limiting endpoint controls
every real Z above the threshold. The denominator is the actual positive log 3. -/
theorem tail_phase_enclosure (minimum Z a b lower upper : ℝ)
    (positive : 0 < minimum) (large : minimum ≤ Z)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (finiteLower : lower ≤ minimum*Real.log ((minimum+b)/(minimum+a))/Real.log 3)
    (finiteUpper : minimum*Real.log ((minimum+b)/(minimum+a))/Real.log 3 ≤ upper)
    (limitLower : lower ≤ (b-a)/Real.log 3)
    (limitUpper : (b-a)/Real.log 3 ≤ upper) :
    lower ≤ Z*Real.log ((Z+b)/(Z+a))/Real.log 3 ∧
      Z*Real.log ((Z+b)/(Z+a))/Real.log 3 ≤ upper := by
  have logPositive : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨lowerBound,upperBound⟩ := tail_log_enclosure minimum Z a b
    positive large aNonnegative bNonnegative
  have lowerFinite := (le_div_iff₀ logPositive).1 finiteLower
  have lowerLimit := (le_div_iff₀ logPositive).1 limitLower
  have upperFinite := (div_le_iff₀ logPositive).1 finiteUpper
  have upperLimit := (div_le_iff₀ logPositive).1 limitUpper
  constructor
  · apply (le_div_iff₀ logPositive).2
    exact (le_min lowerFinite lowerLimit).trans lowerBound
  · apply (div_le_iff₀ logPositive).2
    exact upperBound.trans (max_le upperFinite upperLimit)

/-- Sign-sensitive coefficient multiplication used by the uniform tail cells. -/
theorem coefficient_phase_bounds (coefficient lowerCoefficient upperCoefficient
    value lowerValue upperValue : ℝ)
    (coefficientNonnegative : 0 ≤ coefficient)
    (coefficientLower : lowerCoefficient ≤ coefficient)
    (coefficientUpper : coefficient ≤ upperCoefficient)
    (valueLower : lowerValue ≤ value) (valueUpper : value ≤ upperValue) :
    (if 0 ≤ lowerValue then lowerCoefficient else upperCoefficient)*lowerValue ≤
        coefficient*value ∧
    coefficient*value ≤
      (if 0 ≤ upperValue then upperCoefficient else lowerCoefficient)*upperValue := by
  constructor
  · have first := mul_le_mul_of_nonneg_left valueLower coefficientNonnegative
    split_ifs with sign
    · exact (mul_le_mul_of_nonneg_right coefficientLower sign).trans first
    · exact (mul_le_mul_of_nonpos_right coefficientUpper (le_of_not_ge sign)).trans first
  · have first := mul_le_mul_of_nonneg_left valueUpper coefficientNonnegative
    split_ifs with sign
    · exact first.trans (mul_le_mul_of_nonneg_right coefficientUpper sign)
    · exact first.trans (mul_le_mul_of_nonpos_right coefficientLower (le_of_not_ge sign))

/-- Rational derivative bounds hold for all Z above the threshold, so a finite
coefficient-cell certificate does not substitute a sample for the infinite tail. -/
theorem tail_derivative_bounds (minimum Z length offset coefficient
    lowerCoefficient upperCoefficient q : ℝ)
    (minimumPositive : 0 < minimum) (large : minimum ≤ Z)
    (lengthPositive : 0 < length) (offsetNonnegative : 0 ≤ offset)
    (qNonnegative : 0 ≤ q) (coefficientNonnegative : 0 ≤ lowerCoefficient)
    (coefficientLower : lowerCoefficient ≤ coefficient)
    (coefficientUpper : coefficient ≤ upperCoefficient) :
    lowerCoefficient*q*minimum/(minimum*length+offset+1) ≤
        coefficient*q*Z/(Z*length+offset+1) ∧
    coefficient*(q+1)*Z/(Z*length+offset) ≤ upperCoefficient*(q+1)/length := by
  have zPositive : 0 < Z := lt_of_lt_of_le minimumPositive large
  have coefficientPositive : 0 ≤ coefficient := coefficientNonnegative.trans coefficientLower
  have upperNonnegative : 0 ≤ upperCoefficient := coefficientPositive.trans coefficientUpper
  have denominatorMinimum : 0 < minimum*length+offset+1 := by positivity
  have denominatorZ : 0 < Z*length+offset+1 := by positivity
  have denominatorZZero : 0 < Z*length+offset := by positivity
  have ratioLower : minimum/(minimum*length+offset+1) ≤ Z/(Z*length+offset+1) := by
    apply (div_le_div_iff₀ denominatorMinimum denominatorZ).2
    have orderedProduct := mul_le_mul_of_nonneg_right large (show 0 ≤ offset+1 by positivity)
    nlinarith
  have ratioUpper : Z/(Z*length+offset) ≤ 1/length := by
    apply (div_le_div_iff₀ denominatorZZero lengthPositive).2
    nlinarith
  constructor
  · have first := mul_le_mul_of_nonneg_left ratioLower
      (mul_nonneg coefficientNonnegative qNonnegative)
    have second := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right coefficientLower qNonnegative)
      (show 0 ≤ Z/(Z*length+offset+1) by positivity)
    simpa only [← mul_div_assoc] using first.trans second
  · have first := mul_le_mul_of_nonneg_left ratioUpper
      (mul_nonneg coefficientPositive (show 0 ≤ q+1 by positivity))
    have second := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right coefficientUpper (show 0 ≤ q+1 by positivity))
      (show 0 ≤ 1/length by positivity)
    simpa only [← mul_div_assoc,mul_one] using first.trans second

end LambdaCantor.Integer
