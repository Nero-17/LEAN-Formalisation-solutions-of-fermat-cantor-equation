import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock23_compact_checked : lowRationalBlockCheck 1472 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock23_checked : lowRationalBlockCheck 1472 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 1472 64).symm.trans actualLowPartitionBlock23_compact_checked

end LambdaCantor.RationalPowers
