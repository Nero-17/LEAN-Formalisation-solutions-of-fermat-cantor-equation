import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.LightCore
import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped9.LightData
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grouped9_light_checked : blocksCoverCheck 9 3200 (List.range' 2 108) grouped9LightEntries = true := by
  native_decide

end LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped9
