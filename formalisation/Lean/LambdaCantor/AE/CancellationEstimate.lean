import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory
open scoped NNReal

namespace LambdaCantor.AE

/-- The cancellation step in the annular estimate. Subtracting the inverse
density at zero gains one power of the frequency scale. This lemma states
all integrability assumptions explicitly. -/
theorem integral_zero_mean_kernel_bound
    (kernel density : ℝ → ℝ) {constant : ℝ}
    (hkernel : Integrable kernel volume)
    (hproduct : Integrable (fun point => kernel point * density point) volume)
    (hmoment : Integrable (fun point => |point| * |kernel point|) volume)
    (hzero : ∫ point, kernel point = 0)
    (hbound : ∀ point, |density point - density 0| ≤ constant * |point|) :
    |∫ point, kernel point * density point| ≤
      constant * ∫ point, |point| * |kernel point| := by
  have hconstant : Integrable (fun point => kernel point * density 0) volume :=
    hkernel.mul_const (density 0)
  have hcancellation : (∫ point, kernel point * density point) =
      ∫ point, kernel point * density point - kernel point * density 0 := by
    rw [integral_sub hproduct hconstant, integral_mul_const, hzero, zero_mul, sub_zero]
  rw [hcancellation]
  calc
    |∫ point, kernel point * density point - kernel point * density 0| ≤
        ∫ point, |kernel point * density point - kernel point * density 0| :=
      by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume)
          (fun point : ℝ => kernel point * density point - kernel point * density 0))
    _ ≤ ∫ point, constant * (|point| * |kernel point|) := by
      apply integral_mono (hproduct.sub hconstant).norm (hmoment.const_mul constant)
      intro point
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      rw [← mul_sub, abs_mul]
      calc
        |kernel point| * |density point - density 0| ≤
            |kernel point| * (constant * |point|) :=
          mul_le_mul_of_nonneg_left (hbound point) (abs_nonneg _)
        _ = constant * (|point| * |kernel point|) := by ring
    _ = constant * ∫ point, |point| * |kernel point| := integral_const_mul _ _

/-- Frequency-scaled version used after the change of variables in
equation (pair-annulus). The first moment of the Schwartz kernel is the
fixed constant, and the Lipschitz constant of the inverse density is divided
by the frequency scale. -/
theorem integral_zero_mean_kernel_scaled_bound
    (kernel density : ℝ → ℝ) {constant : ℝ≥0} {frequency : ℝ}
    (hfrequency : 0 < frequency) (hlipschitz : LipschitzWith constant density)
    (hkernel : Integrable kernel volume)
    (hproduct : Integrable (fun point => kernel point * density (point / frequency)) volume)
    (hmoment : Integrable (fun point => |point| * |kernel point|) volume)
    (hzero : ∫ point, kernel point = 0) :
    |∫ point, kernel point * density (point / frequency)| ≤
      ((constant : ℝ) / frequency) * ∫ point, |point| * |kernel point| := by
  apply integral_zero_mean_kernel_bound kernel (fun point => density (point / frequency))
    hkernel hproduct hmoment hzero
  intro point
  have hdist := hlipschitz.dist_le_mul (point / frequency) 0
  simp only [Real.dist_eq, sub_zero, abs_div, abs_of_pos hfrequency, zero_div] at hdist ⊢
  calc
    |density (point / frequency) - density 0| ≤
        (constant : ℝ) * (|point| / frequency) := hdist
    _ = (constant : ℝ) / frequency * |point| := by ring

end LambdaCantor.AE
