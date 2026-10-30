import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock34_compact_checked : lowRationalBlockCheck 2176 10 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock34_checked : lowRationalBlockCheck 2176 10 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 2176 10).symm.trans actualLowPartitionBlock34_compact_checked

end LambdaCantor.RationalPowers
