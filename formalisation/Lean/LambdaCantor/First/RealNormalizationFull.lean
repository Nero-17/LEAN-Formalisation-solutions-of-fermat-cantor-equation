import LambdaCantor.First.RealNormalizationIdentity
import LambdaCantor.First.RealNormalizationConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section
namespace LambdaCantor

/-- Uniform C1 convergence of the actual normalized two-cylinder power
residual. Integer depths may be arbitrary; their actual phase tends to a
positive real limit. No analytic approximation is assumed. -/
theorem tendstoUniformly_realNormalizedResidual (exponent : ℝ) {lower upper phase : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) (hphase : 0 < phase)
    (leftDepth rightDepth padding : ℕ → ℕ)
    (hright : Filter.Tendsto rightDepth Filter.atTop Filter.atTop)
    (hpadding : Filter.Tendsto padding Filter.atTop Filter.atTop)
    (hphases : Filter.Tendsto
      (fun index => (rightDepth index : ℝ) - exponent * (leftDepth index : ℝ))
      Filter.atTop (nhds phase)) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool))) =>
        realNormalizedResidual exponent (leftDepth index) (rightDepth index) (padding index)
          point.2.1 point.2.2 point.1)
      (fun point => (1 - (point.1 : ℝ)) ^ exponent - exponent * (point.1 : ℝ) ^ phase)
      Filter.atTop ∧
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool))) =>
        deriv (realNormalizedResidual exponent (leftDepth index) (rightDepth index) (padding index)
          point.2.1 point.2.2) point.1)
      (fun point => -(exponent * (1 - (point.1 : ℝ)) ^ (exponent - 1)) -
        exponent * (phase * (point.1 : ℝ) ^ (phase - 1))) Filter.atTop := by
  have hleading : TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        firstRootAmplitude (padding index) point.2 point.1 ^ exponent)
      (fun point => (1 - (point.1 : ℝ)) ^ exponent) Filter.atTop :=
    fun entourage hentourage => hpadding.eventually
      (tendstoUniformly_firstRootAmplitude_power exponent hlower hupper hordered entourage hentourage)
  have hleadingD : TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter => firstRootAmplitude (padding index) point.2 parameter ^ exponent) point.1)
      (fun point => -(exponent * (1 - (point.1 : ℝ)) ^ (exponent - 1))) Filter.atTop :=
    fun entourage hentourage => hpadding.eventually
      (tendstoUniformly_firstRootAmplitude_power_derivative exponent hlower hupper hordered entourage hentourage)
  have hleadingPair := hleading.comp
    (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.1))
  have hleadingDPair := hleadingD.comp
    (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.1))
  have hphasePair := ((@Real.uniformContinuous_const_mul exponent).comp_tendstoUniformly
    (tendstoUniformly_phase_power hlower hphases)).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => point.1)
  have hphaseDPair := ((@Real.uniformContinuous_const_mul exponent).comp_tendstoUniformly
    (tendstoUniformly_phase_power_derivative hlower hphases)).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => point.1)
  have hcorrection := tendstoUniformly_real_phase_tail hlower hupper hordered hphase hphases hpadding
  have hcorrectionPair := ((@Real.uniformContinuous_const_mul exponent).comp_tendstoUniformly
    hcorrection.1).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have hcorrectionDPair := ((@Real.uniformContinuous_const_mul exponent).comp_tendstoUniformly
    hcorrection.2).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have herror := tendstoUniformly_realNormalizationError exponent hlower hupper hordered hphase
    hphases hright hpadding
  have herrorPair := herror.1.comp
    (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have herrorDPair := herror.2.comp
    (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have hcombined := ((hleadingPair.sub hphasePair).add hcorrectionPair).add herrorPair
  have hcombinedD := ((hleadingDPair.sub hphaseDPair).add hcorrectionDPair).add herrorDPair
  simp only [Function.comp_def, Pi.sub_apply, Pi.add_apply, mul_zero, add_zero] at hcombined hcombinedD
  have htarget :
      ((((fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) =>
          (1 - (point.1 : ℝ)) ^ exponent) -
        fun point => exponent * (point.1 : ℝ) ^ phase) + fun _ => (0 : ℝ)) + fun _ => (0 : ℝ)) =
      (fun point => (1 - (point.1 : ℝ)) ^ exponent - exponent * (point.1 : ℝ) ^ phase) := by
    funext point
    simp only [Pi.add_apply, Pi.sub_apply, add_zero]
  have htargetD :
      ((((fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) =>
          -(exponent * (1 - (point.1 : ℝ)) ^ (exponent - 1))) -
        fun point => exponent * (phase * (point.1 : ℝ) ^ (phase - 1))) + fun _ => (0 : ℝ)) +
        fun _ => (0 : ℝ)) =
      (fun point => -(exponent * (1 - (point.1 : ℝ)) ^ (exponent - 1)) -
        exponent * (phase * (point.1 : ℝ) ^ (phase - 1))) := by
    funext point
    simp only [Pi.add_apply, Pi.sub_apply, add_zero]
  rw [htarget] at hcombined
  rw [htargetD] at hcombinedD
  constructor
  · apply (tendstoUniformly_congr ?_).mp hcombined
    filter_upwards [hpadding.eventually (Filter.eventually_ge_atTop 1)] with index hi
    funext point
    simp only [Pi.sub_apply, Pi.add_apply]
    exact (realNormalizedResidual_decomposition (lt_of_lt_of_le hlower point.1.property.1)
      (lt_of_le_of_lt point.1.property.2 hupper) (leftDepth index) (rightDepth index)
      (padding index) hi point.2.1 point.2.2).symm
  · apply (tendstoUniformly_congr ?_).mp hcombinedD
    have hsmall := ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (hlower.le.trans hordered) hupper).comp hright).eventually
        (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [hpadding.eventually (Filter.eventually_ge_atTop 1), hsmall] with index hi hj
    funext point
    simp only [Pi.sub_apply, Pi.add_apply]
    exact (realNormalizedResidual_derivative_decomposition
      (lt_of_lt_of_le hlower point.1.property.1) (lt_of_le_of_lt point.1.property.2 hupper)
      (leftDepth index) (rightDepth index) (padding index) hi
      ((pow_le_pow_left₀ (hlower.le.trans point.1.property.1) point.1.property.2 _).trans hj.le)
      point.2.1 point.2.2).symm

end LambdaCantor
