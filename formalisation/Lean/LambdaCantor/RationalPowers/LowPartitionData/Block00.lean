import LambdaCantor.RationalPowers.LowPartitionData.Definitions
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem actualLowPartitionBlock00_checked : lowRationalBlockCheck 0 64 actualLowPartitionPredicate = true := by
  native_decide

end LambdaCantor.RationalPowers
