import LambdaCantor.RationalPowers.LargeExponentRawFull12Coverage
import LambdaCantor.RationalPowers.LargeExponentRawFull13Coverage
import LambdaCantor.RationalPowers.LargeExponentRawFull14Coverage
import Mathlib.Tactic.FinCases

namespace LambdaCantor.RationalPowers

open Integer

/-- Continuous full-phase coverage is shared by the integer and real branches.
Only the three accepted Full12/13/14 data sets are imported here. -/
theorem largeExponent_cached_full_coverage (layer : Fin 3) :
    FiniteCoverageCertified (layer.val+12) := by
  fin_cases layer
  · exact largeExponentRawFull12_coverage
  · exact largeExponentRawFull13_coverage
  · exact largeExponentRawFull14_coverage

#print axioms largeExponent_cached_full_coverage


end LambdaCantor.RationalPowers
