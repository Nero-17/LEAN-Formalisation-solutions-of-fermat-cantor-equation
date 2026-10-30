import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.LightCore
import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Full14.Fused.LightData
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Full14.Fused

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem full14_light_checked : blocksCoverCheck 14 16000 [1] full14LightEntries = true := by
  native_decide

end LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Full14.Fused
