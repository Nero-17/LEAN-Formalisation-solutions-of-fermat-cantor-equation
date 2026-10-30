import LambdaCantor.AE.AlmostEverywhereDyadicEnergy
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
open scoped ENNReal

namespace LambdaCantor.AE

/-- The constructed cutoff covers every frequency of modulus at least one at a dyadic scale. -/
theorem exists_annularCutoff_dyadic_scale {frequency : ℝ} (hfrequency : 1 ≤ |frequency|) :
    ∃ scale : ℕ, (2 : ℝ) ^ scale ≤ |frequency| ∧
      |frequency| < (2 : ℝ) ^ (scale + 1) ∧
      annularCutoff (frequency / (2 : ℝ) ^ scale) = 1 := by
  obtain ⟨scale, hlower, hupper⟩ := exists_nat_pow_near hfrequency (by norm_num : (1 : ℝ) < 2)
  refine ⟨scale, hlower, hupper, annularCutoff_eq_one ?_ ?_⟩
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ scale)]
    exact (one_le_div (by positivity)).mpr hlower
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ scale)]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [show |frequency| < (2 : ℝ) ^ scale * 2 by simpa only [pow_succ] using hupper]

/-- Pointwise high-frequency Sobolev weight comparison with the actual smooth annuli. -/
theorem sobolev_fourier_weight_le_dyadic {regularity frequency : ℝ}
    (hregularity : 0 ≤ regularity) (hfrequency : 1 ≤ |frequency|) (ratio : ℝ) :
    ENNReal.ofReal (|frequency| ^ (2 * regularity) * ‖addressFourier ratio frequency‖ ^ 4) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity)) *
        ∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
          (annularCutoff (frequency / (2 : ℝ) ^ scale) * ‖addressFourier ratio frequency‖ ^ 4)) := by
  obtain ⟨scale, hlower, hupper, hcutoff⟩ := exists_annularCutoff_dyadic_scale hfrequency
  have hpower : |frequency| ^ (2 * regularity) ≤
      (2 : ℝ) ^ (2 * regularity) * ((2 : ℝ) ^ scale) ^ (2 * regularity) := by
    have hle : |frequency| ≤ 2 * (2 : ℝ) ^ scale := by
      simpa only [pow_succ, mul_comm] using hupper.le
    have hbound := Real.rpow_le_rpow (abs_nonneg frequency) hle (by linarith : 0 ≤ 2 * regularity)
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 2 ^ scale)]
      using hbound
  calc
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ (2 * regularity) *
        ((2 : ℝ) ^ scale) ^ (2 * regularity)) * ‖addressFourier ratio frequency‖ ^ 4) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpower (by positivity))
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity)) *
        ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
          (annularCutoff (frequency / (2 : ℝ) ^ scale) * ‖addressFourier ratio frequency‖ ^ 4)) := by
      rw [hcutoff, one_mul, mul_assoc, ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := mul_le_mul_left' (ENNReal.le_tsum scale) _

end LambdaCantor.AE
