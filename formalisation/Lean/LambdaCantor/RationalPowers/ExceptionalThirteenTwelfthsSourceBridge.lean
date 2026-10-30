import LambdaCantor.RationalPowers.ExceptionalThirteenTwelfthsData
import LambdaCantor.RationalPowers.ExceptionalRemainingSourceChecked
import Mathlib.Data.Fintype.Fin
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.RationalPowers.Exceptional.ThirteenTwelfths
def source : PowerSource := RemainingSources.source13_12
theorem source_valid : source.Valid := RemainingSources.source13_12_valid
theorem source_depth_matches : source.returnDepth = maximumDepth := rfl
theorem offsets_exact : ∀ digit : Fin 4, (offsets digit : ℚ)/denominator =
    match digit.val with | 0 => 0 | 1 => 1 | 2 => source.slope | _ => source.slope+1 := by native_decide
theorem outer_intervals_exact :
    outerIntervals.map (fun interval => ((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator)) =
    [(1/3,(source.slope+1)/6),(source.slope/3,(source.slope+3)/6),
      ((source.slope+1)/3,(3*source.slope+1)/6)] := by native_decide
theorem inner_intervals_exact :
    innerIntervals.map (fun interval => ((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator)) =
    [(1/3+source.margin,(source.slope+1)/6-source.margin),
      (source.slope/3+source.margin,(source.slope+3)/6-source.margin),
      ((source.slope+1)/3+source.margin,(3*source.slope+1)/6-source.margin)] := by native_decide
end LambdaCantor.RationalPowers.Exceptional.ThirteenTwelfths
