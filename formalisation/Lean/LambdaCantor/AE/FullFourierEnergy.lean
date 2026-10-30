import LambdaCantor.AE.HighFrequencySobolev
import LambdaCantor.AE.FourierEnergyDefinition

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

theorem fullFourierEnergy_le_highFrequency (ratio : ℝ) {regularity : ℝ}
    (hregularity : 0 ≤ regularity) :
    fullFourierEnergy ratio regularity ≤
      2 * (∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|},
        ENNReal.ofReal (|frequency| ^ (2 * regularity) * ‖addressFourier ratio frequency‖ ^ 4)) + 4 := by
  have hset : MeasurableSet {frequency : ℝ | 1 ≤ |frequency|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hhighBound : (∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|}, ENNReal.ofReal
      ((1 + |frequency| ^ (2 * regularity)) * ‖addressFourier ratio frequency‖ ^ 4)) ≤
      2 * ∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|},
        ENNReal.ofReal (|frequency| ^ (2 * regularity) * ‖addressFourier ratio frequency‖ ^ 4) := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    apply setLIntegral_mono' hset
    intro frequency hfrequency
    have hpower : 1 ≤ |frequency| ^ (2 * regularity) :=
      Real.one_le_rpow hfrequency (by linarith)
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [pow_nonneg (norm_nonneg (addressFourier ratio frequency)) 4]
  have hlowBound : (∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|}ᶜ, ENNReal.ofReal
      ((1 + |frequency| ^ (2 * regularity)) * ‖addressFourier ratio frequency‖ ^ 4)) ≤
      ∫⁻ _ in Ioo (-1 : ℝ) 1, (2 : ℝ≥0∞) := by
    have hcomplement : {frequency : ℝ | 1 ≤ |frequency|}ᶜ = Ioo (-1) 1 := by
      ext frequency
      simp only [mem_compl_iff, mem_setOf_eq, not_le, mem_Ioo, ← abs_lt]
    rw [hcomplement]
    apply setLIntegral_mono' measurableSet_Ioo
    intro frequency hfrequency
    have habs : |frequency| ≤ 1 := (abs_lt.mpr hfrequency).le
    have hpower := Real.rpow_le_one (abs_nonneg frequency) habs (by linarith : 0 ≤ 2 * regularity)
    have hfourth : ‖addressFourier ratio frequency‖ ^ 4 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_addressFourier_le_one _ _)
    have hnonnegative := Real.rpow_nonneg (abs_nonneg frequency) (2 * regularity)
    rw [← (show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [pow_nonneg (norm_nonneg (addressFourier ratio frequency)) 4]
  unfold fullFourierEnergy
  rw [← lintegral_add_compl _ hset]
  calc
    _ ≤ (2 * ∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|},
        ENNReal.ofReal (|frequency| ^ (2 * regularity) * ‖addressFourier ratio frequency‖ ^ 4)) +
        ∫⁻ _ in Ioo (-1 : ℝ) 1, (2 : ℝ≥0∞) := add_le_add hhighBound hlowBound
    _ = _ := by norm_num [Real.volume_Ioo]

theorem fullFourierEnergy_lt_top_of_highFrequency (ratio : ℝ) {regularity : ℝ}
    (hregularity : 0 ≤ regularity)
    (hhigh : (∫⁻ frequency in {frequency : ℝ | 1 ≤ |frequency|},
      ENNReal.ofReal (|frequency| ^ (2 * regularity) * ‖addressFourier ratio frequency‖ ^ 4)) < ∞) :
    fullFourierEnergy ratio regularity < ∞ :=
  (fullFourierEnergy_le_highFrequency ratio hregularity).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hhigh, by norm_num⟩)

theorem ae_finite_fullFourierEnergy
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    ∀ᵐ ratio : ℝ, 0 < parameterCutoff ratio → fullFourierEnergy ratio regularity < ∞ := by
  filter_upwards [ae_finite_highFrequency_sobolev_integral hlower horder hupper hregularity hrange
    parameterCutoff hsmooth hcompact hsupport hnonnegative] with ratio hfinite
  exact fun hpositive => fullFourierEnergy_lt_top_of_highFrequency ratio hregularity (hfinite hpositive)

end LambdaCantor.AE
