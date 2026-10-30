import LambdaCantor.AE.DifferenceSeries

open Filter Topology Set

namespace LambdaCantor.AE

theorem secondDifference_term_bound
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    (index : ℕ) {point upper : ℝ} (hupper : 0 < upper) (hpoint : |point| ≤ upper) :
    ‖coefficients index * (index + 1 : ℕ) * (index : ℝ) * point ^ (index - 1)‖ ≤
      (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index := by
  cases index with
  | zero => simp; positivity
  | succ index =>
    have hpower := pow_le_pow_left₀ (abs_nonneg point) hpoint index
    have hcoefficient := hcoefficients (index + 1)
    calc
      _ = |coefficients (index + 1)| * ((index + 2 : ℕ) : ℝ) *
          ((index + 1 : ℕ) : ℝ) * |point| ^ index := by
            simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, Nat.succ_sub_one,
              Nat.succ_eq_add_one, Nat.add_assoc]
      _ ≤ 2 * ((index + 2 : ℕ) : ℝ) * ((index + 1 : ℕ) : ℝ) * upper ^ index :=
        mul_le_mul (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (by positivity))
          hpower (by positivity) (by positivity)
      _ ≤ 2 * ((index + 2 : ℕ) : ℝ) ^ 2 * upper ^ index := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hupper.le index)
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) index]
      _ = _ := by
        simp only [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]
        field_simp [hupper.ne']
        <;> ring

/-- A second termwise differentiation, with a summable bound uniform on
compact subintervals. This provides the regularity needed in the pair-annulus
change-of-variables estimate. -/
theorem hasDerivAt_deriv_normalizedDifference
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    HasDerivAt (deriv (normalizedDifference coefficients))
      (∑' index : ℕ, coefficients index * (index + 1 : ℕ) * (index : ℝ) *
        ratio ^ (index - 1)) ratio := by
  obtain ⟨upper, hratio, hupper⟩ := exists_between hlt
  have hupperpos := hpos.trans hratio
  have hsum : Summable (fun index : ℕ =>
      (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index) := by
    simpa only [Nat.zero_add, mul_assoc] using
      (summable_shifted_polynomial_geometric 0 2 hupperpos hupper).mul_left (2 / upper)
  have hterms : ∀ index point, point ∈ Ioo (-upper) upper →
      HasDerivAt (fun parameter : ℝ => coefficients index * (index + 1 : ℕ) * parameter ^ index)
        (coefficients index * (index + 1 : ℕ) * (index : ℝ) * point ^ (index - 1)) point := by
    intro index point _
    simpa only [mul_assoc] using
      (hasDerivAt_pow index point).const_mul (coefficients index * (index + 1 : ℕ))
  have hbound : ∀ index point, point ∈ Ioo (-upper) upper →
      ‖coefficients index * (index + 1 : ℕ) * (index : ℝ) * point ^ (index - 1)‖ ≤
        (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index := by
    intro index point hpoint
    exact secondDifference_term_bound coefficients hcoefficients index hupperpos (abs_lt.mpr hpoint).le
  have hbase : Summable (fun index : ℕ => coefficients index * ratio ^ index) := by
    simpa only [pow_zero, mul_one] using
      summable_bounded_polynomial_geometric coefficients hcoefficients 0 hpos hlt
  have hweighted := summable_bounded_polynomial_geometric coefficients hcoefficients 1 hpos hlt
  have hinitial : Summable (fun index : ℕ => coefficients index * (index + 1 : ℕ) * ratio ^ index) := by
    apply (hweighted.add hbase).congr
    intro index
    simp only [pow_one, Nat.cast_add, Nat.cast_one]
    ring
  have hmembership : ratio ∈ Ioo (-upper) upper := by constructor <;> linarith
  have hseries := hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioo
    (convex_Ioo (-upper) upper).isPreconnected hterms hbound hmembership hinitial hmembership
  apply hseries.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hpos hlt] with parameter hparameter
  exact (hasDerivAt_normalizedDifference coefficients hcoefficients hparameter.1 hparameter.2).deriv

/-- Uniform finite bound on the second derivative, with the constant displayed
as a convergent positive series rather than introducing an unspecified O-term. -/
theorem normalizedDifference_secondDerivative_bound
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    {ratio upper : ℝ} (hpos : 0 < ratio) (horder : ratio ≤ upper) (hupper : upper < 1) :
    |deriv (deriv (normalizedDifference coefficients)) ratio| ≤
      ∑' index : ℕ, (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index := by
  have hupperpos := hpos.trans_le horder
  have hsum : Summable (fun index : ℕ =>
      (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index) := by
    simpa only [Nat.zero_add, mul_assoc] using
      (summable_shifted_polynomial_geometric 0 2 hupperpos hupper).mul_left (2 / upper)
  have hbound : ∀ index : ℕ,
      ‖coefficients index * (index + 1 : ℕ) * (index : ℝ) * ratio ^ (index - 1)‖ ≤
        (2 / upper) * ((index + 1 : ℕ) : ℝ) ^ 2 * upper ^ index := by
    intro index
    exact secondDifference_term_bound (point := ratio) coefficients hcoefficients index
      hupperpos (by simpa only [abs_of_pos hpos] using horder)
  rw [(hasDerivAt_deriv_normalizedDifference coefficients hcoefficients hpos
    (horder.trans_lt hupper)).deriv]
  simpa only [Real.norm_eq_abs] using
    (hsum.of_norm_bounded hbound).hasSum.norm_le_of_bounded hsum.hasSum hbound

end LambdaCantor.AE
