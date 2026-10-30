import LambdaCantor.Last.EndpointTransferLogCore

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

def normalizedPowerDrop (exponent coefficient scale coordinate : ℝ) : ℝ :=
  coefficient / exponent * powerDropQuotient exponent scale coordinate

/-- The coordinates are exchanged: reflected v comes first, u comes second.
This is the derivative orientation used by the logarithmic paper source. -/
def logarithmicCylinderSource
    (exponent coefficient scale firstLeft firstScale secondRight secondScale firstCutoff dropCutoff : ℝ)
    (point : ℝ × ℝ) : ℝ :=
  exponent * cutoffLog firstCutoff (firstLeft + firstScale * point.2) -
    cutoffLog dropCutoff
      (normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1))

theorem normalizedPowerDrop_continuous {exponent : ℝ} (hexponent : 1 ≤ exponent)
    (coefficient scale : ℝ) : Continuous (normalizedPowerDrop exponent coefficient scale) := by
  unfold normalizedPowerDrop powerDropQuotient
  apply Continuous.const_mul
  apply Continuous.div_const
  exact continuous_const.sub
    ((continuous_const.sub (continuous_const.mul continuous_id)).rpow_const (fun _ => Or.inr (by linarith)))

theorem logarithmicCylinderSource_continuous {exponent firstCutoff dropCutoff : ℝ}
    (hexponent : 1 ≤ exponent) (hfirstCutoff : 0 < firstCutoff) (hdropCutoff : 0 < dropCutoff)
    (coefficient scale firstLeft firstScale secondRight secondScale : ℝ) :
    Continuous (logarithmicCylinderSource exponent coefficient scale firstLeft firstScale
      secondRight secondScale firstCutoff dropCutoff) := by
  apply Continuous.sub
  · exact ((cutoffLog_continuous hfirstCutoff).comp
      (continuous_const.add (continuous_const.mul continuous_snd))).const_mul exponent
  · exact (cutoffLog_continuous hdropCutoff).comp
      ((normalizedPowerDrop_continuous hexponent coefficient scale).comp
        (continuous_const.sub (continuous_const.mul continuous_fst)))

theorem normalizedPowerDrop_reflected_hasStrictFDerivAt {exponent scale : ℝ}
    (hexponent : 1 ≤ exponent) (hscale : scale ≠ 0)
    (coefficient secondRight secondScale : ℝ) (point : ℝ × ℝ) :
    HasStrictFDerivAt
      (fun value : ℝ × ℝ => normalizedPowerDrop exponent coefficient scale
        (secondRight - secondScale * value.1))
      ((-coefficient * secondScale *
        (1 - scale * secondRight + scale * secondScale * point.1) ^ (exponent - 1)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ) point := by
  have hbase := ((((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := point)).const_mul
    (scale * secondScale)).const_add (1 - scale * secondRight)).rpow_const (Or.inr hexponent))
  have hdrop := ((hasStrictFDerivAt_const (1 : ℝ) point).sub hbase).const_mul
    (coefficient / (exponent * scale))
  refine (hdrop.congr_of_eventuallyEq (Eventually.of_forall ?_)).congr_fderiv ?_
  · intro value
    change coefficient / (exponent * scale) *
      (1 - (1 - scale * secondRight + scale * secondScale * value.1) ^ exponent) =
      normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * value.1)
    unfold normalizedPowerDrop powerDropQuotient
    rw [show 1 - scale * (secondRight - secondScale * value.1) =
      1 - scale * secondRight + scale * secondScale * value.1 by ring]
    have hexponent_nonzero : exponent ≠ 0 := by linarith
    field_simp [hexponent_nonzero, hscale]
    <;> ring
  · apply ContinuousLinearMap.ext
    intro value
    change coefficient / (exponent * scale) *
      (0 - (exponent * (1 - scale * secondRight + scale * secondScale * point.1) ^ (exponent - 1)) *
        ((scale * secondScale) * value.1)) =
      (-coefficient * secondScale *
        (1 - scale * secondRight + scale * secondScale * point.1) ^ (exponent - 1)) * value.1
    have hexponent_nonzero : exponent ≠ 0 := by linarith
    field_simp [hexponent_nonzero, hscale]
    <;> ring

theorem logarithmicCylinderSource_hasStrictFDerivAt
    {exponent scale firstCutoff dropCutoff : ℝ}
    (hexponent : 1 ≤ exponent) (hscale : scale ≠ 0)
    (hfirstCutoff : 0 < firstCutoff) (hdropCutoff : 0 < dropCutoff)
    (coefficient firstLeft firstScale secondRight secondScale : ℝ) (point : ℝ × ℝ)
    (hfirst : firstCutoff < firstLeft + firstScale * point.2)
    (hdrop : dropCutoff < normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1)) :
    HasStrictFDerivAt
      (logarithmicCylinderSource exponent coefficient scale firstLeft firstScale
        secondRight secondScale firstCutoff dropCutoff)
      (((normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1))⁻¹ *
          coefficient * secondScale *
          (1 - scale * secondRight + scale * secondScale * point.1) ^ (exponent - 1)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ +
       (exponent * firstScale / (firstLeft + firstScale * point.2)) •
        ContinuousLinearMap.snd ℝ ℝ ℝ) point := by
  have hfirstAffine :=
    ((hasStrictFDerivAt_snd (𝕜 := ℝ) (p := point)).const_mul firstScale).const_add firstLeft
  have hfirstDerivative :=
    (LambdaCantor.Last.HasStrictFDerivAt.cutoffLog hfirstAffine hfirstCutoff hfirst).const_mul exponent
  have hdropDerivative := LambdaCantor.Last.HasStrictFDerivAt.cutoffLog
    (normalizedPowerDrop_reflected_hasStrictFDerivAt hexponent hscale
      coefficient secondRight secondScale point) hdropCutoff hdrop
  refine ((hfirstDerivative.sub hdropDerivative).congr_of_eventuallyEq
    (Eventually.of_forall ?_)).congr_fderiv ?_
  · intro value
    rfl
  · apply ContinuousLinearMap.ext
    intro value
    change exponent * ((firstLeft + firstScale * point.2)⁻¹ * (firstScale * value.2)) -
      (normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1))⁻¹ *
        ((-coefficient * secondScale *
          (1 - scale * secondRight + scale * secondScale * point.1) ^ (exponent - 1)) * value.1) =
      ((normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1))⁻¹ *
        coefficient * secondScale *
        (1 - scale * secondRight + scale * secondScale * point.1) ^ (exponent - 1)) * value.1 +
      (exponent * firstScale / (firstLeft + firstScale * point.2)) * value.2
    rw [div_eq_mul_inv]
    ring

theorem logarithmic_first_derivative_identity {exponent coefficient scale coordinate secondScale : ℝ}
    (hexponent : exponent ≠ 0) (hcoefficient : coefficient ≠ 0) :
    (normalizedPowerDrop exponent coefficient scale coordinate)⁻¹ * coefficient * secondScale *
      (1 - scale * coordinate) ^ (exponent - 1) =
      secondScale * powerLogDerivative exponent scale coordinate := by
  by_cases hdrop : powerDropQuotient exponent scale coordinate = 0
  · simp [normalizedPowerDrop, powerLogDerivative, hdrop]
  · unfold normalizedPowerDrop powerLogDerivative
    field_simp [hexponent, hcoefficient, hdrop]
    <;> ring

theorem logarithmicCylinderSource_powerLogDerivative
    {exponent scale firstCutoff dropCutoff : ℝ}
    (hexponent : 1 ≤ exponent) (hscale : scale ≠ 0)
    (hfirstCutoff : 0 < firstCutoff) (hdropCutoff : 0 < dropCutoff)
    (coefficient firstLeft firstScale secondRight secondScale : ℝ) (hcoefficient : coefficient ≠ 0)
    (point : ℝ × ℝ) (hfirst : firstCutoff < firstLeft + firstScale * point.2)
    (hdrop : dropCutoff < normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1)) :
    HasStrictFDerivAt
      (logarithmicCylinderSource exponent coefficient scale firstLeft firstScale
        secondRight secondScale firstCutoff dropCutoff)
      ((secondScale * powerLogDerivative exponent scale (secondRight - secondScale * point.1)) •
        ContinuousLinearMap.fst ℝ ℝ ℝ +
       (exponent * firstScale / (firstLeft + firstScale * point.2)) •
        ContinuousLinearMap.snd ℝ ℝ ℝ) point := by
  have hderivative := logarithmicCylinderSource_hasStrictFDerivAt hexponent hscale
    hfirstCutoff hdropCutoff coefficient firstLeft firstScale secondRight secondScale point hfirst hdrop
  have hbase : 1 - scale * secondRight + scale * secondScale * point.1 =
      1 - scale * (secondRight - secondScale * point.1) := by ring
  rw [hbase, logarithmic_first_derivative_identity (show exponent ≠ 0 by linarith) hcoefficient] at hderivative
  exact hderivative

theorem normalizedPowerDrop_limit {exponent coefficient : ℝ} (hexponent : exponent ≠ 0)
    {coefficients scales : ℕ → ℝ} (hscales : ∀ index, 0 < scales index)
    (hscale_limit : Tendsto scales atTop (𝓝 0))
    (hcoefficient_limit : Tendsto coefficients atTop (𝓝 coefficient)) (coordinate : ℝ) :
    Tendsto (fun index => normalizedPowerDrop exponent (coefficients index) (scales index) coordinate)
      atTop (𝓝 (coefficient * coordinate)) := by
  have hwithin : Tendsto scales atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hscale_limit
      (Eventually.of_forall hscales)
  have hlimit := (hcoefficient_limit.div_const exponent).mul ((real_power_drop_limit exponent coordinate).comp hwithin)
  have hidentity : coefficient / exponent * (exponent * coordinate) = coefficient * coordinate := by
    field_simp [hexponent]
  simpa only [normalizedPowerDrop, powerDropQuotient, hidentity, Function.comp_apply] using hlimit

theorem normalizedPowerDrop_mono_on_unit {exponent coefficient scale first second : ℝ}
    (hexponent : 0 < exponent) (hcoefficient : 0 ≤ coefficient) (hscale : 0 < scale)
    (hscale_one : scale < 1) (hfirst : first ∈ Set.Icc (0 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (0 : ℝ) 1) (horder : first ≤ second) :
    normalizedPowerDrop exponent coefficient scale first ≤
      normalizedPowerDrop exponent coefficient scale second := by
  have hbase : 0 ≤ 1 - scale * second := by nlinarith [hsecond.2]
  have hpower := Real.rpow_le_rpow hbase
    (show 1 - scale * second ≤ 1 - scale * first by nlinarith) hexponent.le
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hcoefficient hexponent.le)
  exact div_le_div_of_nonneg_right (by linarith) hscale.le

theorem logarithmicCylinderSource_zero_power_equation
    {exponent coefficient scale firstLeft firstScale secondRight secondScale firstCutoff dropCutoff : ℝ}
    (hexponent : 0 < exponent) (hscale : scale ≠ 0)
    (hfirstCutoff : 0 < firstCutoff) (hdropCutoff : 0 < dropCutoff)
    (point : ℝ × ℝ) (hfirst : firstCutoff ≤ firstLeft + firstScale * point.2)
    (hdrop : dropCutoff ≤ normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1))
    (hzero : logarithmicCylinderSource exponent coefficient scale firstLeft firstScale
      secondRight secondScale firstCutoff dropCutoff point = 0) :
    normalizedCylinderSource exponent coefficient scale firstLeft firstScale secondRight secondScale point.swap = 0 := by
  have hfirst_positive : 0 < firstLeft + firstScale * point.2 := hfirstCutoff.trans_le hfirst
  have hdrop_positive : 0 < normalizedPowerDrop exponent coefficient scale
      (secondRight - secondScale * point.1) := hdropCutoff.trans_le hdrop
  unfold logarithmicCylinderSource at hzero
  rw [cutoffLog_eq hfirst, cutoffLog_eq hdrop] at hzero
  have hlog : Real.log ((firstLeft + firstScale * point.2) ^ exponent) =
      Real.log (normalizedPowerDrop exponent coefficient scale (secondRight - secondScale * point.1)) := by
    rw [Real.log_rpow hfirst_positive]
    linarith
  have hequation := Real.log_injOn_pos (Real.rpow_pos_of_pos hfirst_positive exponent) hdrop_positive hlog
  unfold normalizedCylinderSource
  simp only [Prod.fst_swap, Prod.snd_swap]
  unfold normalizedPowerDrop powerDropQuotient at hequation
  rw [show 1 - scale * secondRight + scale * secondScale * point.1 =
    1 - scale * (secondRight - secondScale * point.1) by ring]
  field_simp [hexponent.ne', hscale] at hequation ⊢
  nlinarith [hequation]

end LambdaCantor.Last

