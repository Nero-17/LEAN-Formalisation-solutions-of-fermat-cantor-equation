import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock22_compact_checked : lowRationalBlockCheck 1408 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock22_checked : lowRationalBlockCheck 1408 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 1408 64).symm.trans actualLowPartitionBlock22_compact_checked

end LambdaCantor.RationalPowers
