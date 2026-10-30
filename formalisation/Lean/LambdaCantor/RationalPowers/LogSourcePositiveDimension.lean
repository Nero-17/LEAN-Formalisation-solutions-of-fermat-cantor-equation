import LambdaCantor.RationalPowers.RealNearAxisSource
import LambdaCantor.RationalPowers.RealNearAxisTangent
import LambdaCantor.Integer.GoodSlopePositiveDimension

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- A checked direct rational log source proves positive Hausdorff dimension
of the actual a/b-power intersection. Every hypothesis is finite source data;
no actual fibre, perfectness, irrational tangent or integer-depth transfer is
assumed. -/
theorem strict_rational_log_source_positive_dimension (numerator denominator : ℕ) (phaseNumerator : ℤ)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (horizontalDepth verticalDepth horizontal vertical : ℕ) (lowerBand upperBand : ℝ)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (horizontal_prefix : ternaryPrefix horizontal horizontalDepth = true)
    (vertical_prefix : ternaryPrefix vertical verticalDepth = true)
    (vertical_bound : vertical+1 ≤ 3^verticalDepth)
    (band_lower : 1 < lowerBand) (band_upper : upperBand < 3) (upper_positive : 0 < upperBand)
    (band_good : ∀ slope : ℝ, lowerBand < slope → slope < upperBand → GoodSlope slope)
    (lower_ratio : lowerBand/vertical < ((numerator : ℝ)/denominator)/(horizontal+1))
    (upper_ratio : ((numerator : ℝ)/denominator)/horizontal < upperBand/(vertical+1))
    (lower_corner : ((phaseNumerator : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log ((horizontal : ℝ)/3^horizontalDepth)-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((vertical+1 : ℝ)/3^verticalDepth) < 0)
    (upper_corner : 0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log ((horizontal+1 : ℝ)/3^horizontalDepth)-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((vertical : ℝ)/3^verticalDepth)) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  obtain ⟨firstDepth, secondDepth, phase_relation, nonempty, compact, no_isolated, uncountable,
    small, residual, slopes⟩ := real_near_axis_perfect_source numerator denominator phaseNumerator
    denominator_positive coprime exponent_gt_one exponent_ne_two
    horizontalDepth verticalDepth horizontal vertical lowerBand upperBand
    horizontal_positive vertical_positive vertical_bound band_lower band_upper upper_positive band_good
    lower_ratio upper_ratio lower_corner upper_corner
  obtain ⟨point, member, irrational⟩ := exists_irrational_tangent _ uncountable _
    (real_near_axis_normalized_tangent_injective ((numerator : ℝ)/denominator)
      ((phaseNumerator : ℝ)/denominator) exponent_gt_one
      horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical phase_relation
      horizontal_positive vertical_positive vertical_bound small residual)
  have first_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num) member.1.1
  have second_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num) member.1.2
  have slope_facts := slopes point.1 first_bounds point.2 second_bounds
  have horizontal_real_positive : (0 : ℝ) < horizontal := by exact_mod_cast horizontal_positive
  obtain ⟨derivative, strict, formula⟩ := realNearAxisLog_hasStrictFDerivAt exponent_gt_one.le
    (by positivity : (1/3 : ℝ)^secondDepth ≠ 0)
    horizontalDepth verticalDepth horizontal vertical point.1 point.2
    (by linarith [first_bounds.1]) (residual _ second_bounds)
  have positive := good_slope_positive_dimension_of_derivative
    (fun value : ℝ × ℝ => realNearAxisLog ((numerator : ℝ)/denominator)
      ((phaseNumerator : ℝ)/denominator) horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth) value.1 value.2)
    0 (((numerator : ℝ)/denominator)/(horizontal+point.1))
      (realNearAxisVertical ((numerator : ℝ)/denominator) vertical ((1/3 : ℝ)^secondDepth) point.2 verticalDepth)
    slope_facts.1 slope_facts.2 irrational ⟨point,member⟩ (no_isolated ⟨point,member⟩) derivative strict formula
  exact positive.trans_le (real_near_axis_dimension_le_intersection ((numerator : ℝ)/denominator)
    ((phaseNumerator : ℝ)/denominator) horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical
    phase_relation horizontal_positive vertical_positive horizontal_prefix vertical_prefix vertical_bound small residual)

end LambdaCantor.RationalPowers

