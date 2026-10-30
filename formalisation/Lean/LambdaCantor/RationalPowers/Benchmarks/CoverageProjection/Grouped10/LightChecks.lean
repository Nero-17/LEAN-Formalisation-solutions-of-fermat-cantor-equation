import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.LightCore
import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped10.LightData
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grouped10_light_checked : blocksCoverCheck 10 6400 (List.range' 2 108) grouped10LightEntries = true := by
  native_decide

end LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped10
