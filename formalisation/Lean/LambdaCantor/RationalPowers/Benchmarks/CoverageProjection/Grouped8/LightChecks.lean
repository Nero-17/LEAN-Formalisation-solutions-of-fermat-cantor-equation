import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.LightCore
import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped8.LightData
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grouped8_light_checked : blocksCoverCheck 8 6400 (List.range' 2 108) grouped8LightEntries = true := by
  native_decide

end LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped8
