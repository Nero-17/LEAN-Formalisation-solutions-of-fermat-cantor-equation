import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock28_compact_checked : lowRationalBlockCheck 1792 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock28_checked : lowRationalBlockCheck 1792 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 1792 64).symm.trans actualLowPartitionBlock28_compact_checked

end LambdaCantor.RationalPowers
