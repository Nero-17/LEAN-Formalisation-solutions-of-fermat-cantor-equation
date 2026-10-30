import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock02_compact_checked : lowRationalBlockCheck 128 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock02_checked : lowRationalBlockCheck 128 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 128 64).symm.trans actualLowPartitionBlock02_compact_checked

end LambdaCantor.RationalPowers
