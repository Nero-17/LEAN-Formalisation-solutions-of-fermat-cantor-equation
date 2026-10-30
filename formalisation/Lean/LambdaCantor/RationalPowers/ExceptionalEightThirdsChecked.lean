import LambdaCantor.RationalPowers.ExceptionalEightThirdsData
/- User-authorized finite native verification. Lean's compiler-evaluation
auxiliary axioms are confined to these checks; DAG soundness is a kernel theorem. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.RationalPowers.Exceptional.EightThirds
open LambdaCantor.Integer.Exceptional
theorem certificate_checked : checkCertificate denominator offsets innerIntervals nodes = true := by
  native_decide
theorem roots_checked : checkRoots outerIntervals nodes roots maximumDepth = true := by
  native_decide
theorem all_outer_levels_two_returns :
    ∀ level ∈ innerTarget denominator outerIntervals,
      TwoReturns (fun digit => (offsets digit : ℝ)/denominator)
        (innerTarget denominator innerIntervals) maximumDepth level :=
  checked_roots_sound denominator offsets innerIntervals outerIntervals nodes roots maximumDepth
    certificate_checked roots_checked
#print axioms all_outer_levels_two_returns
end LambdaCantor.RationalPowers.Exceptional.EightThirds
