import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock08_compact_checked : lowRationalBlockCheck 512 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock08_checked : lowRationalBlockCheck 512 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 512 64).symm.trans actualLowPartitionBlock08_compact_checked

end LambdaCantor.RationalPowers
