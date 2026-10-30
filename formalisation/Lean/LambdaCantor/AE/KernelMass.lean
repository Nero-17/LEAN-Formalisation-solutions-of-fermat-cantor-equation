import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

/-- Cauchy--Schwarz on the set carrying the good parameters. This works
directly with L2 densities and the actual measure of that set. -/
theorem setIntegral_sq_le_measure_mul_norm_sq
    {Domain : Type*} [MeasurableSpace Domain] (measure : Measure Domain)
    (density : Lp ℝ 2 measure) {good : Set Domain}
    (hmeasurable : MeasurableSet good) (hfinite : measure good ≠ ∞) :
    (∫ point in good, density point ∂measure) ^ 2 ≤ measure.real good * ‖density‖ ^ 2 := by
  have hcs := real_inner_mul_inner_self_le
    (indicatorConstLp 2 hmeasurable hfinite (1 : ℝ)) density
  rw [L2.inner_indicatorConstLp_one hmeasurable hfinite density,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hmeasurable hmeasurable hfinite hfinite,
    Set.inter_self, real_inner_self_eq_norm_sq] at hcs
  simpa only [pow_two] using hcs

/-- The quantitative positive-proportion consequence of (density-point-kernel).
A kernel retaining at least half its mass on the good set and having squared
L2 norm at most C/rho forces good parameters to occupy measure rho/(4C). -/
theorem measure_lower_of_kernel_mass
    {Domain : Type*} [MeasurableSpace Domain] (measure : Measure Domain)
    (density : Lp ℝ 2 measure) {good : Set Domain}
    (hmeasurable : MeasurableSet good) (hfinite : measure good ≠ ∞)
    {radius constant : ℝ} (hradius : 0 < radius) (hconstant : 0 < constant)
    (hmass : 1 / 2 ≤ ∫ point in good, density point ∂measure)
    (hnorm : ‖density‖ ^ 2 ≤ constant / radius) :
    radius / (4 * constant) ≤ measure.real good := by
  have hcs := setIntegral_sq_le_measure_mul_norm_sq measure density hmeasurable hfinite
  have hsquare : (1 / 4 : ℝ) ≤ (∫ point in good, density point ∂measure) ^ 2 := by
    nlinarith
  have hmeasure : 0 ≤ measure.real good := ENNReal.toReal_nonneg
  have hbound : (1 / 4 : ℝ) ≤ (measure.real good * constant) / radius := by
    calc
      (1 / 4 : ℝ) ≤ (∫ point in good, density point ∂measure) ^ 2 := hsquare
      _ ≤ measure.real good * ‖density‖ ^ 2 := hcs
      _ ≤ measure.real good * (constant / radius) := mul_le_mul_of_nonneg_left hnorm hmeasure
      _ = (measure.real good * constant) / radius := (mul_div_assoc _ _ _).symm
  have hproduct := (le_div_iff₀ hradius).mp hbound
  apply (div_le_iff₀ (by positivity : 0 < 4 * constant)).mpr
  nlinarith

end LambdaCantor.AE

