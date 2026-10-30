import LambdaCantor.RationalPowers.LargeExponentRawGrouped7Coverage
import LambdaCantor.RationalPowers.LargeExponentRawGrouped8Coverage
import LambdaCantor.RationalPowers.LargeExponentRawGrouped9Coverage
import LambdaCantor.RationalPowers.LargeExponentRawGrouped10Coverage
import LambdaCantor.RationalPowers.LargeExponentRawGrouped11Coverage
import LambdaCantor.RationalPowers.LargeExponentCachedFullLayers
import Mathlib.Tactic.FinCases

namespace LambdaCantor.RationalPowers

open Integer

/-- Every grouped layer retains every denominator from 2 through 109. -/
theorem largeExponent_cached_grouped_coverage (layer : Fin 5) (denominator : Nat)
    (membership : denominator ∈ List.range' 2 108) :
    LargeExponentGroupedCoverageChecked (layer.val+7) denominator := by
  fin_cases layer
  · exact largeExponentRawGrouped7_coverage denominator membership
  · exact largeExponentRawGrouped8_coverage denominator membership
  · exact largeExponentRawGrouped9_coverage denominator membership
  · exact largeExponentRawGrouped10_coverage denominator membership
  · exact largeExponentRawGrouped11_coverage denominator membership

#print axioms largeExponent_cached_grouped_coverage
#print axioms largeExponent_cached_full_coverage


end LambdaCantor.RationalPowers
