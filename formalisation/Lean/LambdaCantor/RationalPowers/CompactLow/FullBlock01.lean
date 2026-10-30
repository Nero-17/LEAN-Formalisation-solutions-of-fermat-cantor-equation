import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers.CompactLow
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The complete second production block, with all235200 original indices. -/
theorem fullBlock01_checked : lowRationalBlockCheck 64 64 predicate = true := by
  native_decide

/-- Return the actual original proposition, using the all-natural equality. -/
theorem fullBlock01_original_checked :
    lowRationalBlockCheck 64 64 actualLowPartitionPredicate = true := by
  rw [← blockCheck_eq]
  exact fullBlock01_checked

end LambdaCantor.RationalPowers.CompactLow

#print axioms LambdaCantor.RationalPowers.CompactLow.fullBlock01_original_checked
