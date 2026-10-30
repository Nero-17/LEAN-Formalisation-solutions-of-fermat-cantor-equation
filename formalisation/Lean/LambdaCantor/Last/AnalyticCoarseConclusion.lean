import LambdaCantor.Last.AnalyticCoarseSmallConclusion
import LambdaCantor.Last.AnalyticCoarseModerateConclusion
import LambdaCantor.Last.AnalyticCoarseCapacityConclusion
import LambdaCantor.Last.AnalyticCoarseLargeConclusion
import LambdaCantor.Last.AnalyticCoarseEndpointWitness

noncomputable section
namespace LambdaCantor.Last

theorem coarse_strict_log_link_all_exponents {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent : 1 < exponent) : CoarseStrictLogLink ratio exponent := by
  by_cases hfirst : exponent ≤ 23 / 19
  · exact coarse_strict_log_link_first_range hlower hupper hexponent hfirst
  by_cases hsecond : exponent ≤ 3
  · exact coarse_strict_log_link_second_range hlower hupper (by linarith) hsecond
  by_cases hmoderate : exponent ≤ 6
  · exact coarse_strict_log_link_moderate_range hlower hupper (by linarith) hmoderate
  by_cases hcapacity : exponent ≤ 20
  · exact coarse_strict_log_link_capacity_range hlower hupper (by linarith) hcapacity
  obtain ⟨coordinate, hcoordinate, shift, hinside⟩ :=
    coarse_large_exponent_strict_link (by linarith) hlower hupper
  exact ⟨shift, Real.log coordinate, ⟨coordinate, hcoordinate, rfl⟩, hinside⟩

/-- Unconditional actual coarse infinitude for every rational exponent above
one, obtained from the actual strict link, perturbed logarithmic Cantor sets,
and canonical shell points. -/
theorem coarse_rational_infinite_intersection {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent : 1 < exponent) {numerator denominator : ℕ}
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hphase : exponent * denominator = numerator) :
    (intersection exponent ratio).Infinite :=
  coarse_rational_infinite_intersection_of_strict_link hlower hupper hexponent
    hnumerator hdenominator hphase
    (coarse_strict_log_link_all_exponents hlower hupper hexponent)

end LambdaCantor.Last
