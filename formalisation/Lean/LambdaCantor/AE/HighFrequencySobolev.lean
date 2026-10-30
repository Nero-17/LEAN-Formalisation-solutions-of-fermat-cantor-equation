import LambdaCantor.AE.FourierMeasurability

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

theorem highFrequency_sobolev_integral_le_dyadic (ratio : ℝ) {regularity : ℝ}
    (hregularity : 0 ≤ regularity) :
    (∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|},
      ENNReal.ofReal (|frequency| ^ (2 * regularity) * ‖addressFourier ratio frequency‖ ^ 4)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity)) *
        ∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
          ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) := by
  have hmeasurable (scale : ℕ) : Measurable (fun frequency : ℝ =>
      ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (annularCutoff (frequency / (2 : ℝ) ^ scale) * ‖addressFourier ratio frequency‖ ^ 4))) :=
    (measurable_const.mul ((contDiff_annularCutoff.continuous.measurable.comp
      (measurable_id.div_const _)).mul ((measurable_addressFourier ratio).norm.pow_const 4))).ennreal_ofReal
  calc
    _ ≤ ∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|},
        ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity)) *
          ∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
            (annularCutoff (frequency / (2 : ℝ) ^ scale) * ‖addressFourier ratio frequency‖ ^ 4)) := by
      apply setLIntegral_mono' (isClosed_le continuous_const continuous_abs).measurableSet
      exact fun frequency hfrequency => sobolev_fourier_weight_le_dyadic hregularity hfrequency ratio
    _ ≤ ∫⁻ frequency : ℝ, ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity)) *
          ∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
            (annularCutoff (frequency / (2 : ℝ) ^ scale) * ‖addressFourier ratio frequency‖ ^ 4)) :=
      setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [lintegral_const_mul _ (Measurable.tsum hmeasurable),
        lintegral_tsum (fun scale => (hmeasurable scale).aemeasurable)]
      congr 1
      apply tsum_congr
      intro scale
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrable_scaled_annularEnergy ratio (by positivity : (0 : ℝ) < 2 ^ scale)).const_mul _)
        (Eventually.of_forall (fun frequency => by
          exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
            (mul_nonneg (annularCutoff_nonneg _) (by positivity)))),
        integral_const_mul, integral_scaled_annularEnergy ratio (by positivity)]

theorem ae_finite_highFrequency_sobolev_integral
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    ∀ᵐ ratio : ℝ, 0 < parameterCutoff ratio →
      (∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|},
        ENNReal.ofReal (|frequency| ^ (2 * regularity) * ‖addressFourier ratio frequency‖ ^ 4)) < ∞ := by
  filter_upwards [ae_finite_dyadic_energy_on_positive_cutoff hlower horder hupper hregularity hrange
    parameterCutoff hsmooth hcompact hsupport hnonnegative] with ratio hfinite
  intro hpositive
  exact (highFrequency_sobolev_integral_le_dyadic ratio hregularity).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinite hpositive))

end LambdaCantor.AE
