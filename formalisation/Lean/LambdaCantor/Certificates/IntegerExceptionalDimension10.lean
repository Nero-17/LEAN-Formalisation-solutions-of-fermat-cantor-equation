import LambdaCantor.Integer.ExceptionalCertifiedDimension
import LambdaCantor.Certificates.IntegerExceptionalVerified10
import LambdaCantor.Certificates.IntegerExceptionalSource10
namespace LambdaCantor.Integer.Exceptional.N10
open LambdaCantor.Integer.Exceptional
theorem positive_dimension : 0 < dimH (intersection 10 (1/3)) := by
  have result := certified_source_positive_dimension source source_valid denominator
    (by norm_num [denominator]) offsets outerIntervals innerIntervals maximumDepth
    source_depth_matches offsets_exact outer_intervals_exact inner_intervals_exact
    all_outer_levels_two_returns
  simpa only [source, Nat.cast_ofNat] using result
#print axioms positive_dimension
end LambdaCantor.Integer.Exceptional.N10
