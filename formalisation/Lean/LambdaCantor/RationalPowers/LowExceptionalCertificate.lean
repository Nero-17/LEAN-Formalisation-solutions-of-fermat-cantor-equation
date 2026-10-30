import LambdaCantor.RationalPowers.LowExceptionalChecks
import LambdaCantor.RationalPowers.ExceptionalCertifiedDimension

namespace LambdaCantor.RationalPowers
open LambdaCantor.Integer.Exceptional

noncomputable section

/-- No exceptional positive-dimension premise occurs here: the conclusion
is obtained from the finite source and both actual DAG checks. -/
theorem LowExceptionalCertificate.Checked.positive_dimension {certificate : LowExceptionalCertificate}
    (checked : certificate.Checked) :
    0 < dimH (intersection ((certificate.numerator : ℝ)/certificate.denominator) (1/3)) := by
  obtain ⟨source_valid, denominator_positive, exponent_equal, depth_equal,
    offsets_exact, outer_exact, inner_exact, certificate_checked, roots_checked, _⟩ := checked
  have result := Exceptional.certified_source_positive_dimension certificate.source source_valid
    certificate.latticeDenominator denominator_positive certificate.offsets certificate.outerIntervals
    certificate.innerIntervals certificate.nodes certificate.roots certificate.maximumDepth depth_equal
    offsets_exact outer_exact inner_exact certificate_checked roots_checked
  rw [exponent_equal] at result
  simpa only [Rat.cast_div, Rat.cast_natCast] using result

end
end LambdaCantor.RationalPowers
