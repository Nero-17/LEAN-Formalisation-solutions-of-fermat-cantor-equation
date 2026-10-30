import LambdaCantor.Integer.ExceptionalSource
import Mathlib.Data.Fintype.Fin
import LambdaCantor.Certificates.IntegerExceptionalData9
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.Integer.Exceptional.N9
open LambdaCantor.Integer.Exceptional
def source : Source :=
  ⟨9, 35468470761712666092, 717894835767785903798754, 42, 50,
    22667127088773175921752637455382704082180262517462889130722362560594047382990365548401870526904555694997514246817526894468880879926614589136283149571237577265601918218081 / 18129252525918438846391243751380085190003440387876467185688063572343845138316314106698547567690664103984716596235277730337080654655893577136115962812791728777997956178176, 21⟩
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
end LambdaCantor.Integer.Exceptional.N9
