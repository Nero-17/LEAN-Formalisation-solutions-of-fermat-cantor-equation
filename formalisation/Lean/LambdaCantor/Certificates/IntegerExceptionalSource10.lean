import LambdaCantor.Integer.ExceptionalSource
import Mathlib.Data.Fintype.Fin
import LambdaCantor.Certificates.IntegerExceptionalData10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.Integer.Exceptional.N10
open LambdaCantor.Integer.Exceptional
def source : Source :=
  ⟨10, 320147672541675873392, 19383220106524103637252896, 44, 53,
    5620222418063892303552788989181062669628011937878070258534815675085315835959210493264889612428975698357029846150874112018297856728540368388916242985673472541775217277629361448593534945116364783183608253565755536912896 / 4487311523703131621538643792031115889823169819317179376050168328787250739447265387640574570415668391537525610591267680855102762087423262683465020172044181404877261081131487595117833574434435180331793417416500353926623, 15⟩
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
end LambdaCantor.Integer.Exceptional.N10
