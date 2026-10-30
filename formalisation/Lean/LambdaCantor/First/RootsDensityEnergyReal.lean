import LambdaCantor.First.RootsDensityEnergy

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

theorem density_fourier_weighted_real_bound (measure : Measure ℝ) [IsFiniteMeasure measure]
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point) (measurable : Measurable density)
    (law : measure = volume.withDensity (fun point => ENNReal.ofReal (density point)))
    (order bound : ℝ) (order_nonnegative : 0 ≤ order) (bound_nonnegative : 0 ≤ bound)
    (energy_bound : (∫⁻ frequency : ℝ, ENNReal.ofReal ((1 + frequency ^ 2) ^ order *
      ‖charFun measure frequency‖ ^ 2)) ≤ ENNReal.ofReal bound) :
    (∫ frequency : ℝ, (1 + frequency ^ 2) ^ order *
      ‖VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => (density point : ℂ)) frequency‖ ^ 2) ≤ (2 : ℝ) ^ order * bound := by
  have integrable := density_fourier_weighted_integrable measure density nonnegative measurable law order
    order_nonnegative (ne_top_of_le_ne_top ENNReal.ofReal_ne_top energy_bound)
  have comparison := (density_fourier_weighted_energy_bound measure density nonnegative measurable law order
    order_nonnegative).trans (mul_le_mul_left' energy_bound (ENNReal.ofReal ((2 : ℝ) ^ order)))
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← ofReal_integral_eq_lintegral_ofReal integrable
      (Filter.Eventually.of_forall (fun frequency =>
        mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)))] at comparison
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg (by norm_num) _) bound_nonnegative)).mp comparison

/-- Linearity for the actual complex-valued density difference, with the
integrability hypotheses needed by the Bochner Fourier integral. -/
theorem density_difference_fourier (left right : ℝ → ℝ)
    (left_integrable : Integrable left volume) (right_integrable : Integrable right volume)
    (frequency : ℝ) :
    VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
      (fun point => (left point : ℂ) - (right point : ℂ)) frequency =
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => (left point : ℂ)) frequency -
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        (fun point => (right point : ℂ)) frequency := by
  unfold VectorFourier.fourierIntegral
  simp_rw [smul_sub]
  apply integral_sub
  · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ frequency).2 left_integrable.ofReal
  · exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ frequency).2 right_integrable.ofReal

end LambdaCantor.First.Roots
