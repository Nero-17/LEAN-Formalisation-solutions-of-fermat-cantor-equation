import LambdaCantor.Last.MassDistributionScaled

noncomputable section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace LambdaCantor

/-- It suffices to establish the Frostman estimate on closed sets. This is useful
for pushforward measures, whose evaluation formula requires measurable sets. -/
theorem dimension_lower_bound_of_closed_mass_distribution
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure X) (exponent : ℝ≥0) (scale constant : ℝ≥0∞)
    (hscale : 0 < scale) (hconstant : constant ≠ 0) (hfinite : constant ≠ ∞)
    (hbound : ∀ subset : Set X, IsClosed subset → ediam subset ≤ scale →
      measure subset ≤ constant * ediam subset ^ (exponent : ℝ))
    {support : Set X} (hpositive : measure support ≠ 0) :
    (exponent : ℝ≥0∞) ≤ dimH support := by
  apply dimension_lower_bound_of_scaled_mass_distribution measure exponent scale constant
    hscale hconstant hfinite _ hpositive
  intro subset hsubset
  have hclosure := hbound (closure subset) isClosed_closure
    (by simpa only [ediam_closure] using hsubset)
  exact (measure_mono subset_closure).trans (by simpa only [ediam_closure] using hclosure)

end LambdaCantor
