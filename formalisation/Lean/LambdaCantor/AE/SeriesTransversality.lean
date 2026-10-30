import LambdaCantor.AE.DifferenceSeries
import LambdaCantor.AE.Transversality

namespace LambdaCantor.AE

/-- Exact cancellation of the quadratic coefficient in the differential
expression used in equation (transversality). -/
theorem normalizedDifference_derivative_identity
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    deriv (normalizedDifference coefficients) ratio -
        (2 / ratio) * normalizedDifference coefficients ratio =
      -(2 / ratio) - coefficients 0 +
        ∑' index : ℕ, (index : ℝ) * coefficients (index + 1) * ratio ^ (index + 1) := by
  have hbase : Summable (fun index : ℕ => coefficients index * ratio ^ index) := by
    simpa only [pow_zero, mul_one] using
      summable_bounded_polynomial_geometric coefficients hcoefficients 0 hpos hlt
  have hweighted : Summable (fun index : ℕ => (index : ℝ) * coefficients index * ratio ^ index) := by
    apply (summable_bounded_polynomial_geometric coefficients hcoefficients 1 hpos hlt).congr
    intro index
    simp only [pow_one]
    ring
  have hresum : Summable (fun index : ℕ => ((index : ℝ) - 1) * coefficients index * ratio ^ index) := by
    apply (hweighted.sub hbase).congr
    intro index
    ring
  have hvalue : (∑' index : ℕ, coefficients index * ratio ^ (index + 1)) =
      ratio * ∑' index : ℕ, coefficients index * ratio ^ index := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro index
    rw [pow_succ]
    ring
  have hderivative : (∑' index : ℕ, coefficients index * (index + 1 : ℕ) * ratio ^ index) =
      (∑' index : ℕ, (index : ℝ) * coefficients index * ratio ^ index) +
        ∑' index : ℕ, coefficients index * ratio ^ index := by
    rw [← hweighted.tsum_add hbase]
    apply tsum_congr
    intro index
    push_cast
    ring
  have hresidual : (∑' index : ℕ, ((index : ℝ) - 1) * coefficients index * ratio ^ index) =
      (∑' index : ℕ, (index : ℝ) * coefficients index * ratio ^ index) -
        ∑' index : ℕ, coefficients index * ratio ^ index := by
    rw [← hweighted.tsum_sub hbase]
    apply tsum_congr
    intro index
    ring
  have hsplit := hresum.tsum_eq_zero_add
  simp only [Nat.cast_zero, zero_sub, neg_mul, one_mul, pow_zero, mul_one,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hsplit
  rw [(hasDerivAt_normalizedDifference coefficients hcoefficients hpos hlt).deriv,
    normalizedDifference, hvalue, hderivative]
  rw [hresidual] at hsplit
  calc
    _ = -(2 / ratio) +
        ((∑' index : ℕ, (index : ℝ) * coefficients index * ratio ^ index) -
          ∑' index : ℕ, coefficients index * ratio ^ index) := by
      field_simp [hpos.ne']
      <;> ring
    _ = _ := by rw [hsplit]; ring

/-- The infinite-series differential bound in equation (transversality),
including all convergence and differentiation obligations. -/
theorem normalizedDifference_derivative_bound
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    deriv (normalizedDifference coefficients) ratio -
        (2 / ratio) * normalizedDifference coefficients ratio ≤
      -(2 / ratio) + 2 + 2 * ratio ^ 2 / (1 - ratio) ^ 2 := by
  have hnorm : ‖ratio‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hpos] using hlt
  have htail : Summable (fun index : ℕ =>
      (index : ℝ) * coefficients (index + 1) * ratio ^ (index + 1)) := by
    have hsum := (summable_bounded_polynomial_geometric (fun index => coefficients (index + 1))
      (fun index => hcoefficients (index + 1)) 1 hpos hlt).mul_left ratio
    apply hsum.congr
    intro index
    simp only [pow_one, pow_succ]
    ring
  have hmajorant : Summable (fun index : ℕ => 2 * ratio * ((index : ℝ) * ratio ^ index)) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.mul_left (2 * ratio)
  have hbound := htail.tsum_le_tsum (g := fun index : ℕ => 2 * ratio * ((index : ℝ) * ratio ^ index))
    (fun index => show (index : ℝ) * coefficients (index + 1) * ratio ^ (index + 1) ≤
      2 * ratio * ((index : ℝ) * ratio ^ index) by
        have hcoefficient := (le_abs_self (coefficients (index + 1))).trans (hcoefficients (index + 1))
        have hmul := mul_le_mul_of_nonneg_right hcoefficient
          (show 0 ≤ (index : ℝ) * ratio ^ (index + 1) by positivity)
        simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul) hmajorant
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one hnorm] at hbound
  rw [normalizedDifference_derivative_identity coefficients hcoefficients hpos hlt]
  have hconstant : -coefficients 0 ≤ 2 := (neg_le_abs (coefficients 0)).trans (hcoefficients 0)
  have hrewrite : 2 * ratio * (ratio / (1 - ratio) ^ 2) = 2 * ratio ^ 2 / (1 - ratio) ^ 2 := by ring
  rw [hrewrite] at hbound
  linarith

/-- Strict transversality of normalized difference series below one half. -/
theorem normalizedDifference_transversality
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    {ratio : ℝ} (hpos : 0 < ratio) (hhalf : ratio < 1 / 2) :
    deriv (normalizedDifference coefficients) ratio -
        (2 / ratio) * normalizedDifference coefficients ratio < 0 :=
  (normalizedDifference_derivative_bound coefficients hcoefficients hpos (by linarith)).trans_lt
    (transversality_bound_neg hpos hhalf)

/-- Uniform transversality on compact parameter intervals. The same small-value
band and derivative margin work for every normalized difference series with
coefficient bound two. -/
theorem normalizedDifference_uniform_transversality
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) :
    ∃ band margin : ℝ, 0 < band ∧ 0 < margin ∧
      ∀ (coefficients : ℕ → ℝ), (∀ index, |coefficients index| ≤ 2) →
        ∀ ratio ∈ Set.Icc lower upper,
          |normalizedDifference coefficients ratio| < band →
            deriv (normalizedDifference coefficients) ratio < -margin := by
  have hupperpos := hlower.trans_le horder
  have hnegative := transversality_bound_neg hupperpos hupper
  have hmarginpos : 0 < -(-(2 / upper) + 2 + 2 * upper ^ 2 / (1 - upper) ^ 2) :=
    neg_pos.mpr hnegative
  refine ⟨(-(-(2 / upper) + 2 + 2 * upper ^ 2 / (1 - upper) ^ 2)) * lower / 4,
    (-(-(2 / upper) + 2 + 2 * upper ^ 2 / (1 - upper) ^ 2)) / 2,
    by positivity, by positivity, ?_⟩
  intro coefficients hcoefficients ratio hratio hsmall
  have hratiopos := hlower.trans_le hratio.1
  apply derivative_neg_of_small_value (value := normalizedDifference coefficients ratio)
    hratiopos hmarginpos
  · have hbound := normalizedDifference_derivative_bound coefficients hcoefficients
      hratiopos (by linarith [hratio.2])
    have hmono := transversality_bound_mono hratiopos hratio.2 hupper
    linarith
  · apply hsmall.trans_le
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
    exact mul_le_mul_of_nonneg_left hratio.1 (neg_nonneg.mpr hnegative.le)

end LambdaCantor.AE
