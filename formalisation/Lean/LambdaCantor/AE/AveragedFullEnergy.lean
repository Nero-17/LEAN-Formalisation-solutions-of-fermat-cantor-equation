import LambdaCantor.AE.FullFourierEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.AE

theorem measurable_joint_address :
    Measurable (fun parameterAndDigits : ℝ × (ℕ → Bool) =>
      address parameterAndDigits.1 parameterAndDigits.2) := by
  unfold address
  apply (measurable_const.sub measurable_fst).mul
  apply Measurable.tsum
  intro index
  have digit_measurable : Measurable
      (fun parameterAndDigits : ℝ × (ℕ → Bool) => parameterAndDigits.2 index) :=
    (measurable_pi_apply index).comp measurable_snd
  exact ((measurable_of_countable (fun digit : Bool => if digit then (1 : ℝ) else 0)).comp
    digit_measurable).mul (measurable_fst.pow_const index)

theorem measurable_joint_addressFourier :
    Measurable (fun parameterAndFrequency : ℝ × ℝ =>
      addressFourier parameterAndFrequency.1 parameterAndFrequency.2) := by
  have character_continuous : Continuous (fun value : ℝ => (Real.fourierChar value : ℂ)) :=
    continuous_subtype_val.comp Real.continuous_fourierChar
  have hmeasurable : Measurable (fun input : (ℝ × ℝ) × (ℕ → Bool) =>
      (Real.fourierChar (-(input.1.2 * address input.1.1 input.2)) : ℂ)) :=
    character_continuous.measurable.comp
      ((measurable_snd.comp measurable_fst).mul
        (measurable_joint_address.comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).neg
  exact hmeasurable.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_fullFourierEnergy (regularity : ℝ) :
    Measurable (fun ratio => fullFourierEnergy ratio regularity) := by
  have absolute_measurable : Measurable
      (fun parameterAndFrequency : ℝ × ℝ => |parameterAndFrequency.2|) :=
    continuous_abs.measurable.comp measurable_snd
  have hmeasurable : Measurable (fun parameterAndFrequency : ℝ × ℝ => ENNReal.ofReal
      ((1 + |parameterAndFrequency.2| ^ (2 * regularity)) *
        ‖addressFourier parameterAndFrequency.1 parameterAndFrequency.2‖ ^ 4)) :=
    ((measurable_const.add (absolute_measurable.pow_const (2 * regularity))).mul
      (measurable_joint_addressFourier.norm.pow_const 4)).ennreal_ofReal
  exact hmeasurable.lintegral_prod_right'

theorem fullFourierEnergy_le_dyadic (ratio : ℝ) {regularity : ℝ}
    (hregularity : 0 ≤ regularity) :
    fullFourierEnergy ratio regularity ≤
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) *
        (∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
          ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))) + 4 := by
  apply (fullFourierEnergy_le_highFrequency ratio hregularity).trans
  rw [mul_assoc]
  exact add_le_add (mul_le_mul_left' (highFrequency_sobolev_integral_le_dyadic ratio hregularity) 2)
    (le_refl 4)

theorem lintegral_cutoff_fullFourierEnergy_lt_top
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hnonnegative : ∀ ratio, 0 ≤ parameterCutoff ratio) :
    (∫⁻ ratio : ℝ, ENNReal.ofReal (parameterCutoff ratio) *
      fullFourierEnergy ratio regularity) < ⊤ := by
  have hcutoff : Integrable parameterCutoff volume :=
    hsmooth.continuous.integrable_of_hasCompactSupport hcompact
  have hintegrable (scale : ℕ) : Integrable (fun ratio =>
      ((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) :=
    (integrable_parameter_annularEnergy parameterCutoff hcutoff _).const_mul _
  have hdyadic := lintegral_cutoff_dyadic_energy_ne_top hlower horder hupper hregularity hrange
    parameterCutoff hsmooth hcompact hsupport hnonnegative
  have hidentity (ratio : ℝ) :
      ENNReal.ofReal (parameterCutoff ratio) *
        (∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
          ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))) =
      ∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
        (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro scale
    rw [← ENNReal.ofReal_mul (hnonnegative ratio)]
    congr 1
    ring
  have hbound (ratio : ℝ) :
      ENNReal.ofReal (parameterCutoff ratio) * fullFourierEnergy ratio regularity ≤
      (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) *
        (∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
          (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))) +
      4 * ENNReal.ofReal (parameterCutoff ratio) := by
    calc
      _ ≤ ENNReal.ofReal (parameterCutoff ratio) *
          ((2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) *
            (∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
              ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))) + 4) :=
        mul_le_mul_left' (fullFourierEnergy_le_dyadic ratio hregularity)
          (ENNReal.ofReal (parameterCutoff ratio))
      _ = (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) *
          (ENNReal.ofReal (parameterCutoff ratio) *
            (∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
              ((2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))))) +
          4 * ENNReal.ofReal (parameterCutoff ratio) := by
        rw [mul_add]
        ac_rfl
      _ = _ := congrArg (fun value : ℝ≥0∞ =>
          (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) * value +
            4 * ENNReal.ofReal (parameterCutoff ratio)) (hidentity ratio)
  apply (lintegral_mono hbound).trans_lt
  calc
    _ = (∫⁻ ratio : ℝ, (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) *
          (∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
            (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))))) +
        (∫⁻ ratio : ℝ, 4 * ENNReal.ofReal (parameterCutoff ratio)) :=
      lintegral_add_left'
        (f := fun ratio : ℝ => (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) *
          (∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
            (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))))
        (aemeasurable_const.mul
          (AEMeasurable.tsum (fun scale => (hintegrable scale).aemeasurable.ennreal_ofReal)))
        (fun ratio : ℝ => 4 * ENNReal.ofReal (parameterCutoff ratio))
    _ = (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity))) *
          (∫⁻ ratio : ℝ, ∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
            (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale)))) +
        4 * (∫⁻ ratio : ℝ, ENNReal.ofReal (parameterCutoff ratio)) :=
      congrArg₂ (fun first second : ℝ≥0∞ => first + second)
        (lintegral_const_mul' (2 * ENNReal.ofReal ((2 : ℝ) ^ (2 * regularity)))
          (fun ratio : ℝ => ∑' scale : ℕ, ENNReal.ofReal (((2 : ℝ) ^ scale) ^ (2 * regularity) *
            (parameterCutoff ratio * (2 : ℝ) ^ scale * annularEnergy ratio ((2 : ℝ) ^ scale))))
          (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))
        (lintegral_const_mul' 4 (fun ratio : ℝ => ENNReal.ofReal (parameterCutoff ratio))
          (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) (lt_top_iff_ne_top.mpr hdyadic),
      ENNReal.mul_lt_top (by norm_num)
        ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnonnegative)).mp hcutoff.hasFiniteIntegral)⟩

end LambdaCantor.AE
