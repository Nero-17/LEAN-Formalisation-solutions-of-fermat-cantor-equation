import LambdaCantor.AE.CenteredUniform
import LambdaCantor.AE.CenteredC2Decay

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

/-- Uniform strict negativity for all paired addresses on a shrinking
parameter window, derived from actual residual derivatives. -/
theorem centered_uniform_negative_derivative {exponent center lower upper width : ℝ}
    (hexponent : 1 < exponent) (hcenter : 0 < center) (hcenterLess : center < 1)
    (hlower : 0 < lower) (hcenterBand : center ∈ Set.Icc lower upper) (hless : upper < 1)
    (hwidth : 0 ≤ width) (horizontalDepth verticalDepth : ℕ → ℕ)
    (hdepth : ∀ index, index ≤ verticalDepth index)
    (hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index +
      Real.log exponent / Real.log center| ≤ (center ^ index) ^ 2)
    (hremainder : ∀ ratios : ℕ → ℝ, (∀ index, ratios index ∈ Set.Icc lower upper) →
      ∀ digits : ℕ → ℕ → Bool,
        Tendsto (fun index => centeredRemainderFirst exponent (horizontalDepth index)
          (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0)) :
    ∀ᶠ index : ℕ in atTop, ∀ digits ratio,
      ratio ∈ Set.Icc lower upper → |ratio - center| ≤ width * center ^ index →
      deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index)
        index digits) ratio <
        (-exponent * (-Real.log exponent / Real.log center) *
          center ^ (-Real.log exponent / Real.log center - 1)) / 2 := by
  have hdiscrepancy := centered_resonance_exponent_positive hexponent hcenter hcenterLess
  have hexponentPositive : 0 < exponent := by linarith
  have hlimitNegative : -exponent * (-Real.log exponent / Real.log center) *
      center ^ (-Real.log exponent / Real.log center - 1) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hexponentPositive) hdiscrepancy)
      (Real.rpow_pos_of_pos hcenter _)
  apply centered_eventually_uniform_lt
    (fun index digits ratio => deriv (centeredNormalizedResidual exponent (horizontalDepth index)
      (verticalDepth index) index digits) ratio)
    hcenterBand hwidth (fun index => center ^ index) (fun _ => pow_nonneg hcenter.le _)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hcenter.le hcenterLess) (by linarith :
      -exponent * (-Real.log exponent / Real.log center) *
        center ^ (-Real.log exponent / Real.log center - 1) <
      (-exponent * (-Real.log exponent / Real.log center) *
        center ^ (-Real.log exponent / Real.log center - 1)) / 2)
  intro digits ratios hratios hratioLimit
  apply centeredNormalizedResidual_derivative_limit hcenter hlower
    (hcenterBand.1.trans hcenterBand.2) hless horizontalDepth verticalDepth hdepth
    ratios hratios hratioLimit digits
  · apply centered_phase_tendsto hcenter hcenterLess horizontalDepth verticalDepth
    intro index
    simpa only [neg_div, sub_neg_eq_add] using hphase index
  · exact hremainder ratios hratios (fun index position => (digits index position).2)

theorem centered_uniform_derivative_upper_bound {exponent center lower upper width : ℝ}
    (hcenter : 0 < center) (hcenterLess : center < 1)
    (hlower : 0 < lower) (hcenterBand : center ∈ Set.Icc lower upper) (hless : upper < 1)
    (hwidth : 0 ≤ width) (horizontalDepth verticalDepth : ℕ → ℕ)
    (hdepth : ∀ index, index ≤ verticalDepth index)
    (hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index +
      Real.log exponent / Real.log center| ≤ (center ^ index) ^ 2)
    (hremainder : ∀ ratios : ℕ → ℝ, (∀ index, ratios index ∈ Set.Icc lower upper) →
      ∀ digits : ℕ → ℕ → Bool,
        Tendsto (fun index => centeredRemainderFirst exponent (horizontalDepth index)
          (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0)) :
    ∀ᶠ index : ℕ in atTop, ∀ digits ratio,
      ratio ∈ Set.Icc lower upper → |ratio - center| ≤ width * center ^ index →
      |deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index)
        index digits) ratio| ≤
        |-exponent * (-Real.log exponent / Real.log center) *
          center ^ (-Real.log exponent / Real.log center - 1)| + 1 := by
  apply centered_eventually_uniform_abs_bound
    (fun index digits ratio => deriv (centeredNormalizedResidual exponent (horizontalDepth index)
      (verticalDepth index) index digits) ratio)
    hcenterBand hwidth (fun index => center ^ index) (fun _ => pow_nonneg hcenter.le _)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hcenter.le hcenterLess)
  intro digits ratios hratios hratioLimit
  apply centeredNormalizedResidual_derivative_limit hcenter hlower
    (hcenterBand.1.trans hcenterBand.2) hless horizontalDepth verticalDepth hdepth
    ratios hratios hratioLimit digits
  · apply centered_phase_tendsto hcenter hcenterLess horizontalDepth verticalDepth
    intro index
    simpa only [neg_div, sub_neg_eq_add] using hphase index
  · exact hremainder ratios hratios (fun index position => (digits index position).2)

end LambdaCantor.AE
