import LambdaCantor.RationalPowers.CompactLow.Bridge
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock11_compact_checked : lowRationalBlockCheck 704 64 CompactLow.predicate = true := by
  native_decide

theorem actualLowPartitionBlock11_checked : lowRationalBlockCheck 704 64 actualLowPartitionPredicate = true :=
  (CompactLow.blockCheck_eq 704 64).symm.trans actualLowPartitionBlock11_compact_checked

end LambdaCantor.RationalPowers
