import LambdaCantor.Last.MassDistribution

noncomputable section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace LambdaCantor

/-- The mass distribution principle with an arbitrary finite positive constant.
This is deduced from Mathlib, not asserted as an external theorem. -/
theorem dimension_lower_bound_of_scaled_mass_distribution
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure X) (exponent : ℝ≥0) (scale constant : ℝ≥0∞)
    (hscale : 0 < scale) (hconstant : constant ≠ 0) (hfinite : constant ≠ ∞)
    (hbound : ∀ subset : Set X, ediam subset ≤ scale →
      measure subset ≤ constant * ediam subset ^ (exponent : ℝ))
    {support : Set X} (hpositive : measure support ≠ 0) :
    (exponent : ℝ≥0∞) ≤ dimH support := by
  apply dimension_lower_bound_of_mass_distribution (constant⁻¹ • measure) exponent scale hscale
  · intro subset hsubset
    simp only [Measure.smul_apply, smul_eq_mul]
    exact (mul_le_mul_left' (hbound subset hsubset) constant⁻¹).trans_eq
      (ENNReal.inv_mul_cancel_left hconstant hfinite)
  · simpa only [Measure.smul_apply, smul_eq_mul] using
      mul_ne_zero (ENNReal.inv_ne_zero.mpr hfinite) hpositive

/-- Strict positivity follows without a numerical normalization of the measure. -/
theorem positive_dimension_of_scaled_mass_distribution
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure X) (exponent : ℝ≥0) (scale constant : ℝ≥0∞)
    (hexponent : 0 < exponent) (hscale : 0 < scale)
    (hconstant : constant ≠ 0) (hfinite : constant ≠ ∞)
    (hbound : ∀ subset : Set X, ediam subset ≤ scale →
      measure subset ≤ constant * ediam subset ^ (exponent : ℝ))
    {support : Set X} (hpositive : measure support ≠ 0) :
    0 < dimH support := by
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hexponent)
    (dimension_lower_bound_of_scaled_mass_distribution measure exponent scale constant
      hscale hconstant hfinite hbound hpositive)

end LambdaCantor
