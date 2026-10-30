import LambdaCantor.First.RootsL1Limit
import LambdaCantor.First.RootsGoodSetExhaustion

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

/-- Absolute continuity of the full actual root law. The compact good sets,
actual replacement bounds, L1 convergence, weak-limit identification and
almost-everywhere exhaustion are supplied by the preceding internal chain. -/
theorem rootFibreData_rootLaw_absolutelyContinuous {exponent : ℝ}
    (data : RootFibreData exponent) : rootLaw data.root ≪ volume := by
  exact rootFibreData_rootLaw_absolutelyContinuous_of_good_sets data
    (rootSobolevGoodSet_root_law_absolutelyContinuous data)

end LambdaCantor.First.Roots
