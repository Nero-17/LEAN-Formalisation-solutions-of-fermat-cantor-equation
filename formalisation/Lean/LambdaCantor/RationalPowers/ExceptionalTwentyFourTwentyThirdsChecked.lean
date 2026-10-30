import LambdaCantor.RationalPowers.ExceptionalTwentyFourTwentyThirdsData
import LambdaCantor.Integer.ExceptionalCertificateRanges
/- User-authorized native arithmetic checks, one per node range.
Every range reads global nodes, and the coverage check is separate.
The kernel range theorem reconstructs the original checker. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.RationalPowers.Exceptional.TwentyFourTwentyThirds
open LambdaCantor.Integer.Exceptional
def checkedRanges : List (ℕ × ℕ) := [(0,512),(512,1024),(1024,1536),(1536,2048),(2048,2560),(2560,3072),(3072,3584),(3584,4088)]
theorem block000_checked :
    checkNodeRange offsets innerIntervals nodes 0 512 = true := by native_decide
theorem block001_checked :
    checkNodeRange offsets innerIntervals nodes 512 1024 = true := by native_decide
theorem block002_checked :
    checkNodeRange offsets innerIntervals nodes 1024 1536 = true := by native_decide
theorem block003_checked :
    checkNodeRange offsets innerIntervals nodes 1536 2048 = true := by native_decide
theorem block004_checked :
    checkNodeRange offsets innerIntervals nodes 2048 2560 = true := by native_decide
theorem block005_checked :
    checkNodeRange offsets innerIntervals nodes 2560 3072 = true := by native_decide
theorem block006_checked :
    checkNodeRange offsets innerIntervals nodes 3072 3584 = true := by native_decide
theorem block007_checked :
    checkNodeRange offsets innerIntervals nodes 3584 4088 = true := by native_decide
theorem ranges_cover : checkRangeCover nodes.size checkedRanges = true := by native_decide
theorem all_ranges_checked : ∀ bounds ∈ checkedRanges,
    checkNodeRange offsets innerIntervals nodes bounds.1 bounds.2 = true := by
  intro bounds membership
  simp only [checkedRanges, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact block000_checked
  · exact block001_checked
  · exact block002_checked
  · exact block003_checked
  · exact block004_checked
  · exact block005_checked
  · exact block006_checked
  · exact block007_checked
theorem certificate_checked : checkCertificate denominator offsets innerIntervals nodes = true :=
  checkCertificate_of_checkedRanges denominator (by norm_num [denominator])
    offsets innerIntervals nodes checkedRanges ranges_cover all_ranges_checked
theorem roots_checked : checkRoots outerIntervals nodes roots maximumDepth = true := by native_decide
theorem all_outer_levels_two_returns :
    ∀ level ∈ innerTarget denominator outerIntervals,
      TwoReturns (fun digit => (offsets digit : ℝ)/denominator)
        (innerTarget denominator innerIntervals) maximumDepth level :=
  checked_roots_sound denominator offsets innerIntervals outerIntervals nodes roots maximumDepth
    certificate_checked roots_checked
#print axioms all_outer_levels_two_returns
end LambdaCantor.RationalPowers.Exceptional.TwentyFourTwentyThirds
