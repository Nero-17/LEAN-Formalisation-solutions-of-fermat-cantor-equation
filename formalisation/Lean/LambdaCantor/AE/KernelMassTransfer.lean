import LambdaCantor.AE.KernelConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace LambdaCantor.AE

/-- Integration over any measurable set is a contraction on real L1. In
particular this applies to the intersection of the good parameter set with
the shrinking root window. -/
theorem abs_setIntegral_sub_le_L1_norm (first second : Lp ℝ 1 volume)
    (parameters : Set ℝ) :
    |(∫ point in parameters, first point) - ∫ point in parameters, second point| ≤
      ‖first - second‖ := by
  rw [← integral_sub (L1.integrable_coeFn first).integrableOn
    (L1.integrable_coeFn second).integrableOn]
  calc
    _ ≤ ∫ point in parameters, |first point - second point| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (fun point : ℝ => first point - second point)
    _ ≤ ∫ point : ℝ, |first point - second point| :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun point => abs_nonneg _))
        ((L1.integrable_coeFn first).sub (L1.integrable_coeFn second)).abs
    _ = ‖first - second‖ := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub first second] with point equality
      rw [equality, Pi.sub_apply, Real.norm_eq_abs]

/-- The convergent affine mixtures transfer the full mass of the true root
law to the first kernel, paying the telescoping errors exactly once. -/
theorem first_kernel_mass_of_summable_increments
    (kernels : ℕ → Lp ℝ 1 volume) (errors : ℕ → ℝ)
    (summable : Summable errors)
    (increments : ∀ depth, ‖kernels (depth + 1) - kernels depth‖ ≤ errors depth)
    (parameters : Set ℝ)
    (root_mass : ∀ density : Lp ℝ 1 volume,
      Tendsto kernels atTop (𝓝 density) → ∫ point in parameters, density point = 1) :
    1 - ∑' depth, errors depth ≤ ∫ point in parameters, kernels 0 point := by
  obtain ⟨density, convergence, error⟩ :=
    l1_kernel_limit_of_summable_increments volume kernels errors summable increments
  have mass := root_mass density convergence
  have transfer := abs_setIntegral_sub_le_L1_norm density (kernels 0) parameters
  rw [mass] at transfer
  have one_sided := (le_abs_self
    (1 - ∫ point in parameters, kernels 0 point)).trans (transfer.trans error)
  linarith

/-- If the total replacement error vanishes with cylinder length, the first
kernel eventually retains at least half its mass on the good parameters.
This is the mass input used by the Cauchy--Schwarz density contradiction. -/
theorem eventually_first_kernel_half_mass
    (kernels : ℕ → ℕ → Lp ℝ 1 volume) (errors : ℕ → ℕ → ℝ)
    (summable : ∀ length, Summable (errors length))
    (increments : ∀ length depth,
      ‖kernels length (depth + 1) - kernels length depth‖ ≤ errors length depth)
    (parameters : ℕ → Set ℝ)
    (root_mass : ∀ length density,
      Tendsto (kernels length) atTop (𝓝 density) →
        ∫ point in parameters length, density point = 1)
    (vanishing : Tendsto (fun length => ∑' depth, errors length depth) atTop (𝓝 0)) :
    ∀ᶠ length in atTop,
      1 / 2 ≤ ∫ point in parameters length, kernels length 0 point := by
  have small := vanishing.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [small] with length small
  have transfer := first_kernel_mass_of_summable_increments
    (kernels length) (errors length) (summable length) (increments length)
    (parameters length) (root_mass length)
  linarith

end LambdaCantor.AE
