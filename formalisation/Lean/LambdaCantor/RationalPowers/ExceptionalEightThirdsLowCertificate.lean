import LambdaCantor.RationalPowers.LowExceptionalChecks
import LambdaCantor.RationalPowers.ExceptionalEightThirdsChecked
import LambdaCantor.RationalPowers.ExceptionalEightThirdsSource

namespace LambdaCantor.RationalPowers.Exceptional.EightThirds

/-- Reuse the exact same checked source and DAG; the certificate stores
references to their definitions rather than transcribing another array. -/
def lowCertificate : LowExceptionalCertificate where
  numerator := 8
  denominator := 3
  source := source
  latticeDenominator := denominator
  offsets := offsets
  outerIntervals := outerIntervals
  innerIntervals := innerIntervals
  nodes := nodes
  roots := roots
  maximumDepth := maximumDepth

theorem lowCertificate_checked : lowCertificate.Checked := by
  refine ⟨source_valid, ?_, ?_, source_depth_matches, offsets_exact,
    outer_intervals_exact, inner_intervals_exact, certificate_checked, roots_checked, ?_⟩
  · norm_num [lowCertificate, denominator]
  · norm_num [lowCertificate, source, PowerSource.exponent]
  · norm_num [lowCertificate, RealPowers.rationalExceptionalPairs]

#print axioms lowCertificate_checked
end LambdaCantor.RationalPowers.Exceptional.EightThirds
