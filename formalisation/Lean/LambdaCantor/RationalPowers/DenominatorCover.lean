import LambdaCantor.Integer.TernaryPrefixSoundness
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Decide
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! Exact sixteen-source cover from companion commit
9ec893bcef7a71504234be897a16949c0a1f8313,
cantor-dust/work/thirdreal20261021_rational_latticecover_optimized.json.
This module verifies arithmetic, legal Cantor prefixes, and every open join.
It does not use the Python success receipt as an assumption. -/
namespace LambdaCantor.RationalPowers

structure DenominatorSource where
  horizontal : ℕ
  vertical : ℕ
  lowerSlope : ℚ
  upperSlope : ℚ
  lower : ℚ
  upper : ℚ
deriving DecidableEq

def denominatorSources (index : Fin 16) : DenominatorSource :=
  match index.val with
  | 0 => ⟨180, 222, 89/73, 171/137, 22263/22300, 30780/30551⟩
  | 1 => ⟨224, 180, 137/171, 73/89, 729/724, 16352/16109⟩
  | 2 => ⟨180, 218, 89/73, 171/137, 16109/15914, 10260/10001⟩
  | 3 => ⟨182, 218, 89/73, 171/137, 16287/15914, 10374/10001⟩
  | 4 => ⟨216, 168, 137/171, 73/89, 4247/4104, 15768/15041⟩
  | 5 => ⟨186, 218, 89/73, 171/137, 16643/15914, 10602/10001⟩
  | 6 => ⟨162, 242, 89/57, 171/89, 14507/13794, 114/89⟩
  | 7 => ⟨182, 224, 89/57, 171/89, 5429/4256, 3458/2225⟩
  | 8 => ⟨186, 188, 89/57, 171/89, 16643/10716, 1178/623⟩
  | 9 => ⟨224, 186, 89/57, 171/89, 2225/1178, 38304/16643⟩
  | 10 => ⟨240, 164, 89/57, 171/89, 21449/9348, 2736/979⟩
  | 11 => ⟨242, 162, 89/57, 171/89, 89/38, 41382/14507⟩
  | 12 => ⟨504, 216, 89/73, 171/137, 44945/15768, 12312/4247⟩
  | 13 => ⟨512, 216, 89/73, 171/137, 1691/584, 87552/29729⟩
  | 14 => ⟨222, 182, 137/57, 219/89, 30551/10374, 16206/5429⟩
  | _ => ⟨540, 222, 89/73, 171/137, 66543/22300, 92340/30551⟩

def DenominatorSource.Checked (source : DenominatorSource) : Prop :=
  0 < source.horizontal ∧ 0 < source.vertical ∧
  Integer.ternaryPrefix source.horizontal 6 = true ∧
  Integer.ternaryPrefix source.vertical 6 = true ∧
  source.horizontal + 1 ≤ 3^6 ∧ source.vertical + 1 ≤ 3^6 ∧
  0 < source.lowerSlope ∧ source.lowerSlope < source.upperSlope ∧
  source.lowerSlope * (source.horizontal + 1) / source.vertical ≤ source.lower ∧
  source.upper ≤ source.upperSlope * source.horizontal / (source.vertical + 1) ∧
  (11/1100 - 1/(source.vertical+1)) * (source.horizontal+1) ≤ source.lower

instance denominatorSourceCheckedDecidable (source : DenominatorSource) : Decidable source.Checked := by
  unfold DenominatorSource.Checked
  infer_instance

theorem denominatorSources_checked : ∀ index, (denominatorSources index).Checked := by
  native_decide

/-- The actual open intervals, with all sixteen joins checked over the reals. -/
theorem denominatorSources_cover (normalized : ℝ)
    (lower : 1 ≤ normalized) (upper : normalized ≤ 3) :
    ∃ index : Fin 16,
      ((denominatorSources index).lower : ℝ) < normalized ∧
      normalized < ((denominatorSources index).upper : ℝ) := by
  by_cases before0 : normalized < (30780/30551 : ℝ)
  · refine ⟨0, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before0
  by_cases before1 : normalized < (16352/16109 : ℝ)
  · refine ⟨1, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before1
  by_cases before2 : normalized < (10260/10001 : ℝ)
  · refine ⟨2, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before2
  by_cases before3 : normalized < (10374/10001 : ℝ)
  · refine ⟨3, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before3
  by_cases before4 : normalized < (15768/15041 : ℝ)
  · refine ⟨4, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before4
  by_cases before5 : normalized < (10602/10001 : ℝ)
  · refine ⟨5, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before5
  by_cases before6 : normalized < (114/89 : ℝ)
  · refine ⟨6, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before6
  by_cases before7 : normalized < (3458/2225 : ℝ)
  · refine ⟨7, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before7
  by_cases before8 : normalized < (1178/623 : ℝ)
  · refine ⟨8, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before8
  by_cases before9 : normalized < (38304/16643 : ℝ)
  · refine ⟨9, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before9
  by_cases before10 : normalized < (2736/979 : ℝ)
  · refine ⟨10, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before10
  by_cases before11 : normalized < (41382/14507 : ℝ)
  · refine ⟨11, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before11
  by_cases before12 : normalized < (12312/4247 : ℝ)
  · refine ⟨12, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before12
  by_cases before13 : normalized < (87552/29729 : ℝ)
  · refine ⟨13, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before13
  by_cases before14 : normalized < (16206/5429 : ℝ)
  · refine ⟨14, ?_, ?_⟩
    · norm_num [denominatorSources]
      linarith
    · simpa [denominatorSources] using before14
  refine ⟨15, ?_, ?_⟩
  · norm_num [denominatorSources]
    linarith
  · norm_num [denominatorSources]
    linarith

/-- Each normalized exponent has a legal source whose full slope rectangle
and elementary logarithmic-width lower bound are simultaneously strict. -/
theorem normalized_denominator_source (normalized : ℝ)
    (lower : 1 ≤ normalized) (upper : normalized ≤ 3) :
    ∃ index : Fin 16,
      let source := denominatorSources index
      source.Checked ∧
      (source.lowerSlope : ℝ) * (source.horizontal+1) / source.vertical < normalized ∧
      normalized < (source.upperSlope : ℝ) * source.horizontal / (source.vertical+1) ∧
      (11/1100 - 1/((source.vertical : ℝ)+1)) * (source.horizontal+1) < normalized := by
  obtain ⟨index, above, below⟩ := denominatorSources_cover normalized lower upper
  have checked := denominatorSources_checked index
  refine ⟨index, checked, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (by exact_mod_cast checked.2.2.2.2.2.2.2.2.1) above
  · exact lt_of_lt_of_le below (by exact_mod_cast checked.2.2.2.2.2.2.2.2.2.1)
  · have casted :
        (((11/1100 - 1/((denominatorSources index).vertical+1 : ℚ))*
          ((denominatorSources index).horizontal+1 : ℚ) : ℚ) : ℝ) ≤
        ((denominatorSources index).lower : ℝ) :=
      (Rat.cast_le (K := ℝ)).mpr checked.2.2.2.2.2.2.2.2.2.2
    push_cast at casted
    exact lt_of_le_of_lt casted above

end LambdaCantor.RationalPowers

