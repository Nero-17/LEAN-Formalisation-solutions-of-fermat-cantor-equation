import LambdaCantor.AE.DyadicFourierCover
import LambdaCantor.AE.FourierEnergyDefinition

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

theorem norm_addressFourier_le_one (ratio frequency : ℝ) : ‖addressFourier ratio frequency‖ ≤ 1 := by
  unfold addressFourier
  apply (norm_integral_le_integral_norm _).trans
  simp only [Circle.norm_coe, integral_const, measureReal_univ_eq_one, one_smul, le_refl]

theorem integrable_scaled_annularEnergy (ratio : ℝ) {frequency : ℝ} (hfrequency : 0 < frequency) :
    Integrable (fun integrationVariable : ℝ => annularCutoff (integrationVariable / frequency) *
      ‖addressFourier ratio integrationVariable‖ ^ 4) := by
  have hbase : Integrable (fun integrationVariable : ℝ =>
      annularCutoff integrationVariable * ‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4) := by
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using
      Complex.reCLM.integrable_comp (integrable_annularEnergy_integrand ratio frequency)
  convert hbase.comp_mul_left' (inv_ne_zero hfrequency.ne') using 1
  ext integrationVariable
  congr 2 <;> field_simp

theorem integral_scaled_annularEnergy (ratio : ℝ) {frequency : ℝ} (hfrequency : 0 < frequency) :
    (∫ integrationVariable : ℝ, annularCutoff (integrationVariable / frequency) *
      ‖addressFourier ratio integrationVariable‖ ^ 4) = frequency * annularEnergy ratio frequency := by
  have hchange := Measure.integral_comp_inv_mul_left
    (fun integrationVariable : ℝ => annularCutoff integrationVariable *
      ‖addressFourier ratio (integrationVariable * frequency)‖ ^ 4) frequency
  simp only [abs_of_pos hfrequency, smul_eq_mul] at hchange
  convert hchange using 1
  · congr 1
    ext integrationVariable
    congr 2 <;> field_simp
  · rfl

end LambdaCantor.AE
