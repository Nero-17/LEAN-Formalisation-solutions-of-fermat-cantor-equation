import LambdaCantor.Integer.FixedLogSources
import Mathlib.Tactic.FinCases

namespace LambdaCantor.Integer

/-- Pure decoder: certificate payloads are literal strings, never external IO. -/
def base64Digit (character : Char) : ℕ :=
  if 'A' ≤ character ∧ character ≤ 'Z' then character.toNat-'A'.toNat
  else if 'a' ≤ character ∧ character ≤ 'z' then character.toNat-'a'.toNat+26
  else if '0' ≤ character ∧ character ≤ '9' then character.toNat-'0'.toNat+52
  else if character = '+' then 62 else 63

def decodeBase64 (word : String) : ℕ :=
  word.toList.foldl (fun value character => 64*value+base64Digit character) 0

def decodePackedLogSource (word : ℕ) : LogSourceData :=
  { d := word % 2^32
    P := word / 2^32 % 2^32
    Q := word / 2^64 % 2^32
    p := word / 2^96 % 2^8
    q := word / 2^104 % 2^8
    band := ⟨word / 2^112 % 16 % 10,Nat.mod_lt _ (by decide)⟩ }

def decodePackedLogExponent (word : ℕ) : ℕ := word / 2^116 % 16

def decodePackedLogTable (payload : String) : Array ℕ :=
  ((payload.splitOn ".").map decodeBase64).toArray

def LogSourceData.GeometryChecked (n : ℕ) (source : LogSourceData) : Prop :=
  3 ≤ n ∧ 0 < source.P ∧ 0 < source.Q ∧
  ternaryPrefix source.P source.p = true ∧
  ternaryPrefix source.Q source.q = true ∧
  source.P+1 ≤ 3^source.p ∧ source.Q+1 ≤ 3^source.q ∧
  (logSourceBand source.band).1*(source.P+1) <
    (logSourceBand source.band).2.1*n*source.Q ∧
  (logSourceBand source.band).2.2.2*n*(source.Q+1) <
    (logSourceBand source.band).2.2.1*source.P

instance (n : ℕ) (source : LogSourceData) : Decidable (source.GeometryChecked n) := by
  unfold LogSourceData.GeometryChecked
  infer_instance

theorem LogSourceData.GeometryChecked.full_ratio_bounds {n : ℕ} {source : LogSourceData}
    (checked : source.GeometryChecked n) :
    ((logSourceBand source.band).1 : ℝ)/(logSourceBand source.band).2.1 <
        (n : ℝ)*source.Q/(source.P+1) ∧
    (n : ℝ)*(source.Q+1)/source.P <
        ((logSourceBand source.band).2.2.1 : ℝ)/(logSourceBand source.band).2.2.2 := by
  obtain ⟨_,positiveP,_,_,_,_,_,lower,upper⟩ := checked
  have denominators : 0 < (logSourceBand source.band).2.1 ∧
      0 < (logSourceBand source.band).2.2.2 := by
    have allBands : ∀ band : Fin 10, 0 < (logSourceBand band).2.1 ∧
        0 < (logSourceBand band).2.2.2 := by decide
    exact allBands source.band
  constructor
  · apply (div_lt_div_iff₀ (by exact_mod_cast denominators.1)
      (by positivity : (0 : ℝ) < source.P+1)).2
    have converted : ((logSourceBand source.band).1 : ℝ) * (source.P+1) <
        (logSourceBand source.band).2.1 * n * source.Q := by exact_mod_cast lower
    simpa only [mul_comm, mul_left_comm, mul_assoc] using converted
  · apply (div_lt_div_iff₀ (by exact_mod_cast positiveP)
      (by exact_mod_cast denominators.2)).2
    have converted : ((logSourceBand source.band).2.2.2 : ℝ) * n * (source.Q+1) <
        (logSourceBand source.band).2.2.1 * source.P := by exact_mod_cast upper
    simpa only [mul_comm, mul_left_comm, mul_assoc] using converted

def packedLogTableCheck (start : ℕ) (table : Array ℕ) : Bool :=
  (List.range table.size).all fun index =>
    let word := table[index]!
    decide ((decodePackedLogSource word).GeometryChecked (start+index) ∧
      (decodePackedLogSource word).LogChecked (start+index) (decodePackedLogExponent word))

theorem packedLogTableCheck_sound (start : ℕ) (table : Array ℕ)
    (checked : packedLogTableCheck start table = true)
    (n : ℕ) (lower : start ≤ n) (upper : n < start+table.size) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      ∃ exponent, source.LogChecked n exponent := by
  have indexBound : n-start < table.size := by omega
  have row := List.all_eq_true.mp checked (n-start) (List.mem_range.mpr indexBound)
  have identity : start+(n-start) = n := by omega
  simp only [identity,decide_eq_true_eq] at row
  exact ⟨decodePackedLogSource table[n-start]!,row.1,
    decodePackedLogExponent table[n-start]!,row.2⟩

end LambdaCantor.Integer
