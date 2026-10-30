import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace LambdaCantor

/-- The mass-distribution step for a normalized diameter bound. The small-set
estimate is required for all sets, so no measurability convention is hidden. -/
theorem dimension_lower_bound_of_mass_distribution
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure X) (exponent : ℝ≥0) (scale : ℝ≥0∞)
    (hscale : 0 < scale)
    (hbound : ∀ subset : Set X, ediam subset ≤ scale →
      measure subset ≤ ediam subset ^ (exponent : ℝ))
    {support : Set X} (hpositive : measure support ≠ 0) :
    (exponent : ℝ≥0∞) ≤ dimH support := by
  apply le_dimH_of_hausdorffMeasure_ne_zero
  intro hzero
  have hdomination := Measure.le_hausdorffMeasure (exponent : ℝ) measure scale hscale hbound
  exact hpositive (le_antisymm (hdomination support |>.trans_eq hzero) bot_le)

/-- Any strictly positive Frostman exponent gives positive Hausdorff dimension. -/
theorem positive_dimension_of_mass_distribution
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure X) (exponent : ℝ≥0) (scale : ℝ≥0∞)
    (hexponent : 0 < exponent) (hscale : 0 < scale)
    (hbound : ∀ subset : Set X, ediam subset ≤ scale →
      measure subset ≤ ediam subset ^ (exponent : ℝ))
    {support : Set X} (hpositive : measure support ≠ 0) :
    0 < dimH support := by
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hexponent)
    (dimension_lower_bound_of_mass_distribution measure exponent scale hscale hbound hpositive)

end LambdaCantor




