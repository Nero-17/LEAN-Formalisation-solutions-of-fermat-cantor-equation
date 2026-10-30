import LambdaCantor.RationalPowers.LowExceptionalChecks
import LambdaCantor.RationalPowers.ExceptionalFiftyThreeHalvesChecked
import LambdaCantor.RationalPowers.ExceptionalFiftyThreeHalvesSourceBridge
namespace LambdaCantor.RationalPowers.Exceptional.FiftyThreeHalves
def lowCertificate : LowExceptionalCertificate where
  numerator := 53
  denominator := 2
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
  · norm_num [lowCertificate, source, RemainingSources.source53_2, PowerSource.exponent]
  · norm_num [lowCertificate, RealPowers.rationalExceptionalPairs]
#print axioms lowCertificate_checked
end LambdaCantor.RationalPowers.Exceptional.FiftyThreeHalves
