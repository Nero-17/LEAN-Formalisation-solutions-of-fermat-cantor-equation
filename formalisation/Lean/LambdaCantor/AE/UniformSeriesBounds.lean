import LambdaCantor.AE.SecondDifferenceSeries

namespace LambdaCantor.AE

/-- A uniform C² bound for all the normalized series arising from address
pairs. The constant is obtained from convergent positive geometric moments. -/
theorem normalizedDifference_uniform_C2_bounds {upper : ℝ} (hpos : 0 < upper) (hlt : upper < 1) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ coefficients : ℕ → ℝ, (∀ index, |coefficients index| ≤ 2) →
        ∀ ratio ∈ Set.Ioc (0 : ℝ) upper,
          |normalizedDifference coefficients ratio| ≤ constant ∧
          |deriv (normalizedDifference coefficients) ratio| ≤ constant ∧
          |deriv (deriv (normalizedDifference coefficients)) ratio| ≤ constant := by
  have hvalueSummable : Summable (fun index : ℕ => 2 * upper ^ (index + 1)) := by
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      (summable_geometric_of_lt_one hpos.le hlt).mul_left (2 * upper)
  have hfirstSummable : Summable (fun index : ℕ => 2 * ((index + 1 : ℕ) : ℝ) * upper ^ index) := by
    simpa only [Nat.zero_add, pow_one, mul_assoc] using
      (summable_shifted_polynomial_geometric 0 1 hpos hlt).mul_left 2
  have hsecondSummable : Summable (fun index : ℕ =>
      (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index) := by
    simpa only [Nat.zero_add, mul_assoc] using
      (summable_shifted_polynomial_geometric 0 2 hpos hlt).mul_left (2 / upper)
  have hvalueNonneg : 0 ≤ ∑' index : ℕ, 2 * upper ^ (index + 1) := tsum_nonneg (fun _ => by positivity)
  have hfirstNonneg : 0 ≤ ∑' index : ℕ, 2 * ((index + 1 : ℕ) : ℝ) * upper ^ index :=
    tsum_nonneg (fun _ => by positivity)
  have hsecondNonneg : 0 ≤ ∑' index : ℕ, (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index :=
    tsum_nonneg (fun _ => by positivity)
  refine ⟨1 + (∑' index : ℕ, 2 * upper ^ (index + 1)) +
      (∑' index : ℕ, 2 * ((index + 1 : ℕ) : ℝ) * upper ^ index) +
      (∑' index : ℕ, (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index), by linarith, ?_⟩
  intro coefficients hcoefficients ratio hratio
  have hvalueTerms : ∀ index : ℕ, ‖coefficients index * ratio ^ (index + 1)‖ ≤
      2 * upper ^ (index + 1) := by
    intro index
    rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs, abs_of_pos hratio.1]
    exact mul_le_mul (hcoefficients index)
      (pow_le_pow_left₀ hratio.1.le hratio.2 (index + 1)) (pow_nonneg hratio.1.le _) (by norm_num)
  have hvalueBound := (hvalueSummable.of_norm_bounded hvalueTerms).hasSum.norm_le_of_bounded
    hvalueSummable.hasSum hvalueTerms
  have hfirstTerms : ∀ index : ℕ,
      ‖coefficients index * (index + 1 : ℕ) * ratio ^ index‖ ≤
        2 * ((index + 1 : ℕ) : ℝ) * upper ^ index := by
    intro index
    simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, abs_of_pos hratio.1]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (hcoefficients index) (Nat.cast_nonneg _))
      (pow_le_pow_left₀ hratio.1.le hratio.2 index) (pow_nonneg hratio.1.le _) (by positivity)
  have hfirstBound := (hfirstSummable.of_norm_bounded hfirstTerms).hasSum.norm_le_of_bounded
    hfirstSummable.hasSum hfirstTerms
  have hsecondBound := normalizedDifference_secondDerivative_bound coefficients hcoefficients
    hratio.1 hratio.2 hlt
  refine ⟨?_, ?_, by linarith⟩
  · unfold normalizedDifference
    have htriangle := abs_add_le (1 : ℝ) (∑' index, coefficients index * ratio ^ (index + 1))
    simp only [abs_one, Real.norm_eq_abs] at hvalueBound htriangle
    linarith
  · rw [(hasDerivAt_normalizedDifference coefficients hcoefficients hratio.1 (hratio.2.trans_lt hlt)).deriv]
    simp only [Real.norm_eq_abs] at hfirstBound
    linarith

end LambdaCantor.AE
