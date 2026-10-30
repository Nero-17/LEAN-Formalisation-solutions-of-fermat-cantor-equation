import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.BigOperators

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

theorem withDensity_finite_real_mixture {Index : Type*} [Fintype Index]
    (weight : Index → ℝ) (density : Index → ℝ → ℝ)
    (weight_nonnegative : ∀ index, 0 ≤ weight index)
    (measurable : ∀ index, AEStronglyMeasurable (density index) volume)
    (nonnegative : ∀ index, ∀ᵐ value : ℝ, 0 ≤ density index value) :
    volume.withDensity (fun value => ENNReal.ofReal (∑ index, weight index*density index value)) =
      ∑ index, ENNReal.ofReal (weight index) •
        volume.withDensity (fun value => ENNReal.ofReal (density index value)) := by
  classical
  apply Measure.ext
  intro parameters parameters_measurable
  rw [withDensity_apply _ parameters_measurable, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ parameters_measurable]
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_finsetSum' Finset.univ (fun index _ =>
    ((measurable index).aemeasurable.ennreal_ofReal.const_mul (ENNReal.ofReal (weight index))).restrict)]
  have all_nonnegative : ∀ᵐ value : ℝ, ∀ index, 0 ≤ density index value := ae_all_iff.mpr nonnegative
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae all_nonnegative] with value value_nonnegative
  rw [ENNReal.ofReal_sum_of_nonneg (fun index _ =>
    mul_nonneg (weight_nonnegative index) (value_nonnegative index))]
  apply Finset.sum_congr rfl
  intro index _
  exact ENNReal.ofReal_mul (weight_nonnegative index)

/-- Actual finite probability-law densities can be placed in the real L1
space used by the telescoping and root-law identification arguments. -/
theorem finite_density_mixture_L1 {Index : Type*} [Fintype Index]
    (weight : Index → ℝ) (density : Index → ℝ → ℝ)
    (weight_nonnegative : ∀ index, 0 ≤ weight index)
    (integrable : ∀ index, Integrable (density index))
    (nonnegative : ∀ index, ∀ᵐ value : ℝ, 0 ≤ density index value) :
    ∃ mixture : Lp ℝ 1 volume, 0 ≤ mixture ∧
      (mixture : ℝ → ℝ) =ᵐ[volume] (fun value => ∑ index, weight index*density index value) ∧
      volume.withDensity (fun value => ENNReal.ofReal (mixture value)) =
        ∑ index, ENNReal.ofReal (weight index) •
          volume.withDensity (fun value => ENNReal.ofReal (density index value)) := by
  classical
  have sum_integrable : Integrable (fun value => ∑ index, weight index*density index value) :=
    integrable_finset_sum _ (fun index _ => (integrable index).const_mul (weight index))
  have representative := sum_integrable.coeFn_toL1
  have all_nonnegative : ∀ᵐ value : ℝ, ∀ index, 0 ≤ density index value := ae_all_iff.mpr nonnegative
  refine ⟨sum_integrable.toL1 _, (Lp.coeFn_nonneg _).mp ?_, representative, ?_⟩
  · filter_upwards [representative, all_nonnegative] with value equality value_nonnegative
    rw [equality]
    exact Finset.sum_nonneg (fun index _ => mul_nonneg (weight_nonnegative index) (value_nonnegative index))
  · refine (withDensity_congr_ae (representative.fun_comp ENNReal.ofReal)).trans ?_
    exact withDensity_finite_real_mixture weight density weight_nonnegative
      (fun index => (integrable index).aestronglyMeasurable) nonnegative

end LambdaCantor.AE
