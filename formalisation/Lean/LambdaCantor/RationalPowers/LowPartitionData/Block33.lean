import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock33_compact_checked : lowRationalBlockCheck 2112 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock33_checked : lowRationalBlockCheck 2112 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 2112 64).symm.trans actualLowPartitionBlock33_compact_checked

end LambdaCantor.RationalPowers
