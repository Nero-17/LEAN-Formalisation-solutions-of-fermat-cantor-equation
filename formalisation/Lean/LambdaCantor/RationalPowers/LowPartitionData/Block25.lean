import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock25_compact_checked : lowRationalBlockCheck 1600 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock25_checked : lowRationalBlockCheck 1600 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 1600 64).symm.trans actualLowPartitionBlock25_compact_checked

end LambdaCantor.RationalPowers
