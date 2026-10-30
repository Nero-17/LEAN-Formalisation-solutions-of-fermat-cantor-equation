import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.LightCore
import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped11.LightData
import Lean.Elab.Tactic.Decide

namespace LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem grouped11_light_checked : blocksCoverCheck 11 6400 (List.range' 2 108) grouped11LightEntries = true := by
  native_decide

end LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.Grouped11
