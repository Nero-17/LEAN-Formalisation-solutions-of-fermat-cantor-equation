import LambdaCantor.AE.KernelConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

/-- The actual geometric ratio in the freezing estimate. -/
def freezingRatio (lower upper regularity : ℝ) : ℝ :=
  ((upper ^ 2 / lower) ^ (2 * regularity) /
    upper ^ (1 - Real.log 2 / Real.log (1 / lower))) ^ (1 / (2 * (1 + regularity)))

theorem freezingRatio_bounds {lower upper regularity : ℝ}
    (hlower : 0 < lower) (hupper : 0 < upper) (hregularity : 0 < regularity)
    (hroom : (upper ^ 2 / lower) ^ (2 * regularity) <
      upper ^ (1 - Real.log 2 / Real.log (1 / lower))) :
    0 < freezingRatio lower upper regularity ∧ freezingRatio lower upper regularity < 1 := by
  have hbase : 0 < (upper ^ 2 / lower) ^ (2 * regularity) /
      upper ^ (1 - Real.log 2 / Real.log (1 / lower)) := by positivity
  have hless : (upper ^ 2 / lower) ^ (2 * regularity) /
      upper ^ (1 - Real.log 2 / Real.log (1 / lower)) < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hupper _)).mpr hroom
  exact ⟨Real.rpow_pos_of_pos hbase _, Real.rpow_lt_one hbase.le hless (by positivity)⟩

theorem freezing_depth_factor {lower upper regularity : ℝ}
    (hlower : 0 < lower) (hupper : 0 < upper) (depth : ℕ) :
    ((upper ^ 2 / lower) ^ (2 * regularity) /
      upper ^ (1 - Real.log 2 / Real.log (1 / lower))) ^
        ((depth : ℝ) / (2 * (1 + regularity))) =
      freezingRatio lower upper regularity ^ depth := by
  unfold freezingRatio
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  ring

/-- The paper's exact polynomially corrected depth bound is summable. -/
theorem summable_freezing_increments (shift degree : ℕ)
    {lower upper regularity : ℝ}
    (hlower : 0 < lower) (hupper : 0 < upper) (hregularity : 0 < regularity)
    (hroom : (upper ^ 2 / lower) ^ (2 * regularity) <
      upper ^ (1 - Real.log 2 / Real.log (1 / lower))) :
    Summable (fun depth : ℕ => ((shift + depth + 1 : ℕ) : ℝ) ^ degree *
      ((upper ^ 2 / lower) ^ (2 * regularity) /
        upper ^ (1 - Real.log 2 / Real.log (1 / lower))) ^
          ((depth : ℝ) / (2 * (1 + regularity)))) := by
  obtain ⟨hpositive, hless⟩ := freezingRatio_bounds hlower hupper hregularity hroom
  simpa only [freezing_depth_factor hlower hupper] using
    summable_shifted_polynomial_geometric shift degree hpositive hless

/-- Substituting rho = ratio^shift in the full depth sum gives an error
tending to zero, including its polynomial dependence on the initial depth. -/
theorem freezing_total_error_tendsto_zero (degree : ℕ)
    {ratio lower upper regularity : ℝ}
    (hratio : 0 < ratio) (hratio_one : ratio < 1)
    (hlower : 0 < lower) (hupper : 0 < upper) (hregularity : 0 < regularity)
    (hroom : (upper ^ 2 / lower) ^ (2 * regularity) <
      upper ^ (1 - Real.log 2 / Real.log (1 / lower))) :
    Tendsto (fun shift : ℕ => (ratio ^ shift) ^ (regularity / (1 + regularity)) *
      ∑' depth : ℕ, ((shift + depth + 1 : ℕ) : ℝ) ^ degree *
        ((upper ^ 2 / lower) ^ (2 * regularity) /
          upper ^ (1 - Real.log 2 / Real.log (1 / lower))) ^
            ((depth : ℝ) / (2 * (1 + regularity)))) atTop (𝓝 0) := by
  obtain ⟨hpositive, hless⟩ := freezingRatio_bounds hlower hupper hregularity hroom
  have hdecay : 0 < ratio ^ (regularity / (1 + regularity)) := Real.rpow_pos_of_pos hratio _
  have hdecay_less : ratio ^ (regularity / (1 + regularity)) < 1 :=
    Real.rpow_lt_one hratio.le hratio_one (by positivity)
  have hlimit := total_kernel_error_tendsto_zero degree hpositive hless hdecay hdecay_less
  have hpower (shift : ℕ) : (ratio ^ shift) ^ (regularity / (1 + regularity)) =
      (ratio ^ (regularity / (1 + regularity))) ^ shift := by
    rw [← Real.rpow_natCast_mul hratio.le, ← Real.rpow_mul_natCast hratio.le]
    congr 1
    ring
  simpa only [hpower, freezing_depth_factor hlower hupper] using hlimit

end LambdaCantor.AE
