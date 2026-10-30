import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock32_compact_checked : lowRationalBlockCheck 2048 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock32_checked : lowRationalBlockCheck 2048 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 2048 64).symm.trans actualLowPartitionBlock32_compact_checked

end LambdaCantor.RationalPowers
