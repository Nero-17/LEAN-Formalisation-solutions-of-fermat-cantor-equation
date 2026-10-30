import LambdaCantor.RationalPowers.LogSourcePositiveDimension
import LambdaCantor.RationalPowers.ReciprocalLogSourcePositiveDimension
import LambdaCantor.Integer.LogCertificateTransfer

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- Real-exponent geometry of an existing finite ternary source. The natural
number `d` in the old data is deliberately unused: the rational phase is
supplied separately and realized by the proved rational-depth construction. -/
def LargeExponentGeometryChecked (exponent : ℝ) (source : LogSourceData) : Prop :=
  0 < source.P ∧ 0 < source.Q ∧
  ternaryPrefix source.P source.p = true ∧ ternaryPrefix source.Q source.q = true ∧
  source.P+1 ≤ 3^source.p ∧ source.Q+1 ≤ 3^source.q ∧
  ((logSourceBand source.band).1 : ℝ)/(logSourceBand source.band).2.1 <
    exponent*source.Q/(source.P+1) ∧
  exponent*(source.Q+1)/source.P <
    ((logSourceBand source.band).2.2.1 : ℝ)/(logSourceBand source.band).2.2.2

def largeExponentCenteredLower (exponent center : ℝ) (source : LogSourceData) : ℝ :=
  (Real.log ((source.Q : ℝ)/3^source.q)+
    exponent*Real.log (center/((source.P+1)/3^source.p)))/Real.log 3

def largeExponentCenteredUpper (exponent center : ℝ) (source : LogSourceData) : ℝ :=
  (Real.log (((source.Q : ℝ)+1)/3^source.q)+
    exponent*Real.log (center/((source.P : ℝ)/3^source.p)))/Real.log 3

/-- Finite source geometry and actual rational-phase corners transfer through
the real-power construction. No integer-exponent dimension theorem is used. -/
theorem largeExponent_source_positive_dimension
    (numerator denominator : ℕ) (phaseNumerator : ℤ)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (source : LogSourceData)
    (geometry : LargeExponentGeometryChecked ((numerator : ℝ)/denominator) source)
    (lower_corner : ((phaseNumerator : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log ((source.P : ℝ)/3^source.p)-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((source.Q+1 : ℝ)/3^source.q) < 0)
    (upper_corner : 0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log ((source.P+1 : ℝ)/3^source.p)-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((source.Q : ℝ)/3^source.q)) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  obtain ⟨horizontal_positive,vertical_positive,horizontal_prefix,vertical_prefix,
    _,vertical_bound,lower,upper⟩ := geometry
  have vertical_real_positive : (0 : ℝ) < source.Q := by exact_mod_cast vertical_positive
  have lower_ratio :
      (((logSourceBand source.band).1 : ℝ)/(logSourceBand source.band).2.1)/source.Q <
        ((numerator : ℝ)/denominator)/(source.P+1) := by
    apply (div_lt_iff₀ vertical_real_positive).2
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using lower
  have upper_ratio : ((numerator : ℝ)/denominator)/source.P <
      (((logSourceBand source.band).2.2.1 : ℝ)/(logSourceBand source.band).2.2.2)/(source.Q+1) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < source.Q+1)).2
    simpa only [mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using upper
  by_cases direct : source.band.val < 5
  · obtain ⟨band_lower,band_upper,upper_positive,band_good⟩ := direct_log_band_properties source.band direct
    exact strict_rational_log_source_positive_dimension numerator denominator phaseNumerator
      denominator_positive coprime exponent_gt_one exponent_ne_two source.p source.q source.P source.Q
      _ _ horizontal_positive vertical_positive horizontal_prefix vertical_prefix vertical_bound
      band_lower band_upper upper_positive band_good lower_ratio upper_ratio lower_corner upper_corner
  · obtain ⟨band_lower,band_upper,upper_positive,band_good⟩ := reciprocal_log_band_properties source.band (by omega)
    exact reciprocal_strict_rational_log_source_positive_dimension numerator denominator phaseNumerator
      denominator_positive coprime exponent_gt_one exponent_ne_two source.p source.q source.P source.Q
      _ _ horizontal_positive vertical_positive horizontal_prefix vertical_prefix vertical_bound
      band_lower band_upper upper_positive band_good lower_ratio upper_ratio lower_corner upper_corner

end LambdaCantor.RationalPowers
