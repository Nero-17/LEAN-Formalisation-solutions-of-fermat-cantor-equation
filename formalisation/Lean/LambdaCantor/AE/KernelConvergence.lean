import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Filter Topology

namespace LambdaCantor.AE

/-- Summability of the polynomially corrected geometric error in (ae-summable).
The polynomial exponent may be any natural number, allowing it to dominate
the unspecified fixed polynomial factors in the analytic estimates. -/
theorem summable_shifted_polynomial_geometric (shift degree : ℕ)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    Summable (fun depth : ℕ => ((shift + depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth) := by
  have hbase : Summable (fun depth : ℕ => (depth : ℝ) ^ degree * ratio ^ depth) :=
    summable_pow_mul_geometric_of_norm_lt_one degree
    (r := ratio) (by simpa [Real.norm_eq_abs, abs_of_pos hpos] using hlt)
  have hshift : Summable (fun depth : ℕ => ((shift + 1 + depth : ℕ) : ℝ) ^ degree *
      ratio ^ (shift + 1 + depth)) :=
    hbase.comp_injective (add_right_injective (shift + 1))
  have hscaled := hshift.mul_right (ratio ^ (shift + 1))⁻¹
  apply hscaled.congr
  intro depth
  rw [pow_add ratio (shift + 1) depth]
  have hne : ratio ^ (shift + 1) ≠ 0 := pow_ne_zero _ hpos.ne'
  rw [show shift + 1 + depth = shift + depth + 1 by omega]
  field_simp [hne]

/-- A complete metric-space version of the kernel telescoping argument.
It supplies the limit and a bound from each level by the remaining errors. -/
theorem kernel_limit_of_summable_increments {Space : Type*}
    [MetricSpace Space] [CompleteSpace Space]
    (kernels : ℕ → Space) (errors : ℕ → ℝ)
    (hsum : Summable errors)
    (hincrements : ∀ depth, dist (kernels depth) (kernels (depth + 1)) ≤ errors depth) :
    ∃ density : Space, Tendsto kernels atTop (𝓝 density) ∧
      ∀ depth, dist (kernels depth) density ≤ ∑' remaining, errors (depth + remaining) := by
  obtain ⟨density, hlimit⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable errors hincrements hsum)
  exact ⟨density, hlimit,
    fun depth => dist_le_tsum_of_dist_le_of_tendsto errors hincrements hsum hlimit depth⟩

/-- The actual Banach space of integrable densities can be used in the preceding
argument. The hypotheses are exactly an L1 bound on successive kernels and a
summable numerical majorant. -/
theorem l1_kernel_limit_of_summable_increments
    {Domain : Type*} [MeasurableSpace Domain] (measure : MeasureTheory.Measure Domain)
    (kernels : ℕ → MeasureTheory.Lp ℝ 1 measure) (errors : ℕ → ℝ)
    (hsum : Summable errors)
    (hincrements : ∀ depth, ‖kernels (depth + 1) - kernels depth‖ ≤ errors depth) :
    ∃ density : MeasureTheory.Lp ℝ 1 measure,
      Tendsto kernels atTop (𝓝 density) ∧
      ‖density - kernels 0‖ ≤ ∑' depth, errors depth := by
  have hdist : ∀ depth, dist (kernels depth) (kernels (depth + 1)) ≤ errors depth := by
    intro depth
    rw [dist_comm, dist_eq_norm]
    exact hincrements depth
  obtain ⟨density, hlimit, htail⟩ :=
    kernel_limit_of_summable_increments kernels errors hsum hdist
  refine ⟨density, hlimit, ?_⟩
  simpa only [zero_add, dist_eq_norm, norm_sub_rev] using htail 0

/-- Applying the geometric-polynomial estimate closes the L1 Cauchy step in
equation (ae-summable), once the preceding kernel estimates are established. -/
theorem l1_kernel_limit_of_geometric_increments
    {Domain : Type*} [MeasurableSpace Domain] (measure : MeasureTheory.Measure Domain)
    (kernels : ℕ → MeasureTheory.Lp ℝ 1 measure)
    (shift degree : ℕ) (amplitude ratio : ℝ)
    (hpos : 0 < ratio) (hlt : ratio < 1)
    (hincrements : ∀ depth, ‖kernels (depth + 1) - kernels depth‖ ≤
      amplitude * (((shift + depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth)) :
    ∃ density : MeasureTheory.Lp ℝ 1 measure,
      Tendsto kernels atTop (𝓝 density) ∧
      ‖density - kernels 0‖ ≤
        amplitude * ∑' depth : ℕ, ((shift + depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth := by
  obtain ⟨density, hlimit, hbound⟩ := l1_kernel_limit_of_summable_increments measure kernels
    (fun depth => amplitude * (((shift + depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth))
    ((summable_shifted_polynomial_geometric shift degree hpos hlt).mul_left amplitude)
    hincrements
  exact ⟨density, hlimit, by simpa only [tsum_mul_left] using hbound⟩

/-- The sum over kernel depths grows at most polynomially in the initial
cylinder length. This is the uniform-in-length estimate needed before letting
the initial cylinder length tend to infinity. -/
theorem polynomial_geometric_sum_le (shift degree : ℕ)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    (∑' depth : ℕ, ((shift + depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth) ≤
      ((shift + 1 : ℕ) : ℝ) ^ degree *
        ∑' depth : ℕ, ((depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth := by
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro depth
    have hcompare : ((shift + depth + 1 : ℕ) : ℝ) ≤
        ((shift + 1 : ℕ) : ℝ) * ((depth + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) shift, Nat.cast_nonneg (α := ℝ) depth]
    calc
      ((shift + depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth
          ≤ (((shift + 1 : ℕ) : ℝ) * ((depth + 1 : ℕ) : ℝ)) ^ degree *
              ratio ^ depth :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcompare degree)
          (pow_nonneg hpos.le depth)
      _ = ((shift + 1 : ℕ) : ℝ) ^ degree *
          (((depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth) := by rw [mul_pow]; ring
  · exact summable_shifted_polynomial_geometric shift degree hpos hlt
  · simpa only [Nat.zero_add] using
      (summable_shifted_polynomial_geometric 0 degree hpos hlt).mul_left
        (((shift + 1 : ℕ) : ℝ) ^ degree)

/-- The total telescoping error vanishes as the initial cylinder length grows:
exponential decay in that length absorbs its polynomial correction. -/
theorem total_kernel_error_tendsto_zero (degree : ℕ)
    {ratio decay : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1)
    (hdecaypos : 0 < decay) (hdecaylt : decay < 1) :
    Tendsto (fun shift : ℕ => decay ^ shift *
      ∑' depth : ℕ, ((shift + depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth)
      atTop (𝓝 0) := by
  have hvanish : Tendsto
      (fun shift : ℕ => ((shift + 1 : ℕ) : ℝ) ^ degree * decay ^ shift)
      atTop (𝓝 0) := by
    simpa only [Nat.zero_add] using
      (summable_shifted_polynomial_geometric 0 degree hdecaypos hdecaylt).tendsto_atTop_zero
  apply squeeze_zero
  · intro shift
    exact mul_nonneg (pow_nonneg hdecaypos.le shift)
      (tsum_nonneg (fun depth => mul_nonneg (by positivity) (pow_nonneg hpos.le depth)))
  · intro shift
    exact mul_le_mul_of_nonneg_left (polynomial_geometric_sum_le shift degree hpos hlt)
      (pow_nonneg hdecaypos.le shift)
  · convert hvanish.mul_const
      (∑' depth : ℕ, ((depth + 1 : ℕ) : ℝ) ^ degree * ratio ^ depth) using 1
    · ext shift
      ring
    · simp

end LambdaCantor.AE
