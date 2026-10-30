import LambdaCantor.Integer.ExceptionalSource
import Mathlib.Data.Fintype.Fin
import LambdaCantor.Certificates.IntegerExceptionalData31
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.Integer.Exceptional.N31
open LambdaCantor.Integer.Exceptional
def source : Source :=
  ⟨31, 6222085600591088788243970, 6383950808321296014870354, 52, 52,
    8643039521763851250116813607 / 4000000000000000000000000000, 16⟩
theorem source_valid : source.Valid := by native_decide
theorem source_margins_valid : source.MarginValid := by native_decide
theorem source_slope_matches : source.slope = (offsets 2 : ℚ) / denominator := by
  native_decide
theorem offsets_exact : ∀ digit : Fin 4, (offsets digit : ℚ) / denominator =
    match digit.val with
    | 0 => 0
    | 1 => 1
    | 2 => source.slope
    | _ => source.slope + 1 := by native_decide
theorem source_depth_matches : source.returnDepth = maximumDepth := by rfl
theorem outer_intervals_exact :
    outerIntervals.map (fun interval =>
      ((interval.1 : ℚ) / denominator, (interval.2 : ℚ) / denominator)) =
    [(1 / 3, (source.slope + 1) / 6),
     (source.slope / 3, (source.slope + 3) / 6),
     ((source.slope + 1) / 3, (3 * source.slope + 1) / 6)] := by native_decide
theorem inner_intervals_exact :
    innerIntervals.map (fun interval =>
      ((interval.1 : ℚ) / denominator, (interval.2 : ℚ) / denominator)) =
    [(1 / 3 + 1 / 100000, (source.slope + 1) / 6 - 1 / 100000),
     (source.slope / 3 + 1 / 100000, (source.slope + 3) / 6 - 1 / 100000),
     ((source.slope + 1) / 3 + 1 / 100000, (3 * source.slope + 1) / 6 - 1 / 100000)] := by
  native_decide
end LambdaCantor.Integer.Exceptional.N31
