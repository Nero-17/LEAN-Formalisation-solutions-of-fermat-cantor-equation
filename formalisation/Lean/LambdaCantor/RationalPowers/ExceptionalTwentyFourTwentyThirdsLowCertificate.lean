import LambdaCantor.RationalPowers.LowExceptionalChecks
import LambdaCantor.RationalPowers.ExceptionalTwentyFourTwentyThirdsChecked
import LambdaCantor.RationalPowers.ExceptionalTwentyFourTwentyThirdsSourceBridge
namespace LambdaCantor.RationalPowers.Exceptional.TwentyFourTwentyThirds
def lowCertificate : LowExceptionalCertificate where
  numerator := 24
  denominator := 23
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
  · norm_num [lowCertificate, source, RemainingSources.source24_23, PowerSource.exponent]
  · norm_num [lowCertificate, RealPowers.rationalExceptionalPairs]
#print axioms lowCertificate_checked
end LambdaCantor.RationalPowers.Exceptional.TwentyFourTwentyThirds
