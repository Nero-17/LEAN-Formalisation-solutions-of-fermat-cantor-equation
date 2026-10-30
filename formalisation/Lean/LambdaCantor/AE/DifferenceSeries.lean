import LambdaCantor.AE.KernelConvergence
import LambdaCantor.AE.MathlibSmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.NormNum

open Filter Topology Set

namespace LambdaCantor.AE

/-- The normalized address-difference series, with its constant term fixed
at one and all subsequent coefficients bounded by two. -/
noncomputable def normalizedDifference (coefficients : ℕ → ℝ) (ratio : ℝ) : ℝ :=
  1 + ∑' index : ℕ, coefficients index * ratio ^ (index + 1)

theorem summable_bounded_polynomial_geometric
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    (degree : ℕ) {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    Summable (fun index : ℕ => coefficients index * (index : ℝ) ^ degree * ratio ^ index) := by
  have hbase : Summable (fun index : ℕ => 2 * ((index : ℝ) ^ degree * ratio ^ index)) :=
    (summable_pow_mul_geometric_of_norm_lt_one degree
      (r := ratio) (by simpa [Real.norm_eq_abs, abs_of_pos hpos] using hlt)).mul_left 2
  apply hbase.of_norm_bounded
  intro index
  calc
    ‖coefficients index * (index : ℝ) ^ degree * ratio ^ index‖
        = |coefficients index| * (index : ℝ) ^ degree * ratio ^ index := by
          simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast, abs_of_pos hpos]
    _ ≤ 2 * ((index : ℝ) ^ degree * ratio ^ index) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (hcoefficients index) (show 0 ≤ (index : ℝ) ^ degree * ratio ^ index by positivity)

/-- The address-difference series can be differentiated term by term on the
open unit interval. The proof uses a summable uniform derivative bound on a
larger symmetric interval, rather than assuming differentiability. -/
theorem hasDerivAt_normalizedDifference
    (coefficients : ℕ → ℝ) (hcoefficients : ∀ index, |coefficients index| ≤ 2)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    HasDerivAt (normalizedDifference coefficients)
      (∑' index : ℕ, coefficients index * (index + 1 : ℕ) * ratio ^ index) ratio := by
  obtain ⟨upper, hratio, hupper⟩ := exists_between hlt
  have hupperpos : 0 < upper := hpos.trans hratio
  have hsum : Summable (fun index : ℕ => 2 * ((index + 1 : ℕ) : ℝ) * upper ^ index) := by
    simpa only [Nat.zero_add, pow_one, mul_assoc] using
      (summable_shifted_polynomial_geometric 0 1 hupperpos hupper).mul_left 2
  have hterms : ∀ index point, point ∈ Ioo (-upper) upper →
      HasDerivAt (fun parameter : ℝ => coefficients index * parameter ^ (index + 1))
        (coefficients index * (index + 1 : ℕ) * point ^ index) point := by
    intro index point _
    convert (hasDerivAt_pow (index + 1) point).const_mul (coefficients index) using 1 <;>
      first | rfl | simp only [Nat.add_sub_cancel, mul_assoc]
  have hbound : ∀ index point, point ∈ Ioo (-upper) upper →
      ‖coefficients index * (index + 1 : ℕ) * point ^ index‖ ≤
        2 * ((index + 1 : ℕ) : ℝ) * upper ^ index := by
    intro index point hpoint
    have habs : |point| ≤ upper := (abs_lt.mpr hpoint).le
    calc
      ‖coefficients index * (index + 1 : ℕ) * point ^ index‖
          = |coefficients index| * ((index + 1 : ℕ) : ℝ) * |point| ^ index := by
            simp only [norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast]
      _ ≤ 2 * ((index + 1 : ℕ) : ℝ) * upper ^ index :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hcoefficients index) (by positivity))
          (pow_le_pow_left₀ (abs_nonneg point) habs index) (by positivity) (by positivity)
  have hzero : (0 : ℝ) ∈ Ioo (-upper) upper := ⟨neg_neg_of_pos hupperpos, hupperpos⟩
  have hzeroSum : Summable (fun index : ℕ => coefficients index * (0 : ℝ) ^ (index + 1)) := by
    simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  have hseries := hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioo (convex_Ioo (-upper) upper).isPreconnected
    hterms hbound hzero hzeroSum (show ratio ∈ Ioo (-upper) upper by constructor <;> linarith)
  convert hseries.const_add 1 using 1 <;> first | rfl | simp only [normalizedDifference, zero_add]

end LambdaCantor.AE

