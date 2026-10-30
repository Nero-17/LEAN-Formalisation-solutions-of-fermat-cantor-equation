import LambdaCantor.Certificates.IntegerLogSourceDefinition
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace LambdaCantor.Integer

private theorem uncancel_power_three (a b x y : ℕ)
    (comparison : 3^(a-b)*x < y*3^(b-a)) : 3^a*x < y*3^b := by
  rcases le_total a b with hab | hba
  · have power : 3^b = 3^a * 3^(b-a) := by
      rw [← pow_add, Nat.add_sub_of_le hab]
    simp only [Nat.sub_eq_zero_of_le hab, pow_zero, one_mul] at comparison
    have multiplied := Nat.mul_lt_mul_of_pos_left comparison
      (pow_pos (by decide : 0 < (3 : ℕ)) a)
    rw [power]
    nlinarith
  · have power : 3^a = 3^b * 3^(a-b) := by
      rw [← pow_add, Nat.add_sub_of_le hba]
    simp only [Nat.sub_eq_zero_of_le hba, pow_zero, mul_one] at comparison
    have multiplied := Nat.mul_lt_mul_of_pos_left comparison
      (pow_pos (by decide : 0 < (3 : ℕ)) b)
    rw [power]
    nlinarith

/-- Removal of the common power of three used to keep finite certificates small. -/
theorem LogSourceData.uncancelled_corners {n : ℕ} {source : LogSourceData}
    (valid : source.Valid n) :
    3^(source.d+source.q)*source.P^n < n*(source.Q+1)*3^(source.p*n) ∧
    n*source.Q*3^(source.p*n) < 3^(source.d+source.q)*(source.P+1)^n := by
  obtain ⟨_, _, _, _, _, _, _, lower, upper, _, _⟩ := valid
  constructor
  · exact uncancel_power_three _ _ _ _ lower
  · have reversed := uncancel_power_three (source.p*n) (source.d+source.q)
      (n*source.Q) ((source.P+1)^n) (by simpa [Nat.mul_comm] using upper)
    simpa [Nat.mul_comm] using reversed

private theorem band_denominators_positive (band : Fin 10) :
    0 < (logSourceBand band).2.1 ∧ 0 < (logSourceBand band).2.2.2 := by
  fin_cases band <;> decide

/-- The exact whole derivative interval required by the logarithmic source
predicate. This applies to every pair of coordinates in the closed parent
rectangle, not just the value of the ratio along the zero curve. -/
theorem LogSourceData.full_ratio_bounds {n : ℕ} {source : LogSourceData}
    (valid : source.Valid n) :
    ((logSourceBand source.band).1 : ℝ) / (logSourceBand source.band).2.1 <
        (n : ℝ)*source.Q/(source.P+1) ∧
    (n : ℝ)*(source.Q+1)/source.P <
        ((logSourceBand source.band).2.2.1 : ℝ) / (logSourceBand source.band).2.2.2 := by
  obtain ⟨_, positive, _, _, _, _, _, _, _, lower, upper⟩ := valid
  obtain ⟨denominatorLower, denominatorUpper⟩ := band_denominators_positive source.band
  have positiveReal : (0 : ℝ) < source.P := by exact_mod_cast positive
  constructor
  · apply (div_lt_div_iff₀ (by exact_mod_cast denominatorLower)
        (by positivity : (0 : ℝ) < source.P+1)).2
    have converted : ((logSourceBand source.band).1 : ℝ)*(source.P+1) <
        (logSourceBand source.band).2.1*n*source.Q := by exact_mod_cast lower
    simpa only [mul_comm,mul_left_comm,mul_assoc] using converted
  · apply (div_lt_div_iff₀ positiveReal
        (by exact_mod_cast denominatorUpper)).2
    have converted : ((logSourceBand source.band).2.2.2 : ℝ)*n*(source.Q+1) <
        (logSourceBand source.band).2.2.1*source.P := by exact_mod_cast upper
    simpa only [mul_comm,mul_left_comm,mul_assoc] using converted

/-- The checked natural corner signs are precisely the strict source signs
on the real ternary parent rectangle, before taking the increasing logarithm. -/
theorem LogSourceData.real_corners {n : ℕ} {source : LogSourceData}
    (valid : source.Valid n) :
    (3 : ℝ)^source.d * ((source.P : ℝ)/3^source.p)^n <
      (n : ℝ)*((source.Q+1)/3^source.q) ∧
    (n : ℝ)*((source.Q : ℝ)/3^source.q) <
      (3 : ℝ)^source.d * ((source.P+1)/3^source.p)^n := by
  obtain ⟨lower, upper⟩ := LogSourceData.uncancelled_corners valid
  have lowerReal : (3 : ℝ)^(source.d+source.q)*(source.P : ℝ)^n <
      (n : ℝ)*(source.Q+1)*3^(source.p*n) := by exact_mod_cast lower
  have upperReal : (n : ℝ)*source.Q*3^(source.p*n) <
      (3 : ℝ)^(source.d+source.q)*(source.P+1)^n := by exact_mod_cast upper
  constructor
  · rw [div_pow, ← mul_div_assoc, ← mul_div_assoc]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    simpa only [pow_add, ← pow_mul, mul_assoc, mul_comm, mul_left_comm] using lowerReal
  · rw [div_pow, ← mul_div_assoc, ← mul_div_assoc]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    simpa only [pow_add, ← pow_mul, mul_assoc, mul_comm, mul_left_comm] using upperReal

end LambdaCantor.Integer
