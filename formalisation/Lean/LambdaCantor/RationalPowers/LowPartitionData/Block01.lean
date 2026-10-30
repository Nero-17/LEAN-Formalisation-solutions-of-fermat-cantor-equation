import LambdaCantor.RationalPowers.CompactLow.FullBlock01
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock01_checked : lowRationalBlockCheck 64 64 actualLowPartitionPredicate = true :=
  CompactLow.fullBlock01_original_checked

end LambdaCantor.RationalPowers
