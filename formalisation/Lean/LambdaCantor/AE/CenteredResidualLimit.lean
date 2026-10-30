import LambdaCantor.AE.CenteredTailLimits

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

theorem centered_phase_tendsto {exponent center target : ℝ}
    (hcenter : 0 < center) (hless : center < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index - target| ≤
      (center ^ index) ^ 2) :
    Tendsto (fun index => (verticalDepth index : ℝ) - exponent * horizontalDepth index)
      atTop (𝓝 target) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _ => abs_nonneg _) hphase
  simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0)] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hcenter.le hless).pow 2

theorem centered_resonance_at_center {exponent center : ℝ}
    (hexponent : 0 < exponent) (hcenter : 0 < center) (hless : center < 1) :
    exponent * center ^ (-Real.log exponent / Real.log center) = 1 := by
  have hlog : Real.log center ≠ 0 := ne_of_lt (Real.log_neg hcenter hless)
  have hproduct : Real.log center * (-Real.log exponent / Real.log center) = -Real.log exponent := by
    field_simp [hlog]
    <;> ring
  rw [Real.rpow_def_of_pos hcenter, hproduct, Real.exp_neg, Real.exp_log hexponent]
  exact mul_inv_cancel₀ hexponent.ne'

theorem centered_resonance_exponent_positive {exponent center : ℝ}
    (hexponent : 1 < exponent) (hcenter : 0 < center) (hless : center < 1) :
    0 < -Real.log exponent / Real.log center :=
  div_pos_of_neg_of_neg (neg_neg_of_pos (Real.log_pos hexponent)) (Real.log_neg hcenter hless)

theorem centeredNormalizedResidual_derivative_limit
    {exponent center lower upper discrepancy : ℝ}
    (hcenter : 0 < center) (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ) (hdepth : ∀ index, index ≤ verticalDepth index)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper)
    (hratioLimit : Tendsto ratios atTop (𝓝 center)) (digits : ℕ → ℕ → Bool × Bool)
    (hphase : Tendsto (fun index => (verticalDepth index : ℝ) - exponent * horizontalDepth index)
      atTop (𝓝 discrepancy))
    (hremainder : Tendsto (fun index => centeredRemainderFirst exponent (horizontalDepth index)
      (verticalDepth index) index (fun position => (digits index position).2) (ratios index)) atTop (𝓝 0)) :
    Tendsto (fun index => deriv (centeredNormalizedResidual exponent (horizontalDepth index)
      (verticalDepth index) index (digits index)) (ratios index))
      atTop (𝓝 (-exponent * discrepancy * center ^ (discrepancy - 1))) := by
  have hhorizontal := (centered_factors_tendsto_one hlower hinterval hless ratios hratios
    (fun index position => (digits index position).1)).1
  have htail := (centered_factors_tendsto_one hlower hinterval hless ratios hratios
    (fun index position => (digits index position).2)).2
  have hhorizontalDerivative := (centered_factor_derivatives_tendsto_zero hlower hinterval hless
    ratios hratios (fun index position => (digits index position).1)).1
  have htailDerivative := (centered_factor_derivatives_tendsto_zero hlower hinterval hless
    ratios hratios (fun index position => (digits index position).2)).2
  have hcoefficient := hratioLimit.rpow hphase (Or.inl hcenter.ne')
  have hcoefficientDerivative := hphase.mul
    (hratioLimit.rpow (hphase.sub_const 1) (Or.inl hcenter.ne'))
  have hlimit := (((hhorizontalDerivative.mul_const exponent).mul
      (hhorizontal.rpow_const (p := exponent - 1) (Or.inl (by norm_num)))).sub
        (((hcoefficientDerivative.mul htail).add (hcoefficient.mul htailDerivative)).const_mul exponent)).add
      hremainder
  have hsmall : ∀ᶠ index : ℕ in atTop, upper ^ index < 1 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hlower.le.trans hinterval) hless).eventually
      (gt_mem_nhds zero_lt_one)
  have hhorizontalPositive := hhorizontal.eventually
    (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hidentity : (fun index => deriv (centeredNormalizedResidual exponent (horizontalDepth index)
      (verticalDepth index) index (digits index)) (ratios index)) =ᶠ[atTop]
      (fun index =>
        deriv (centeredHorizontalFactor index (fun position => (digits index position).1)) (ratios index) * exponent *
          (centeredHorizontalFactor index (fun position => (digits index position).1) (ratios index)) ^ (exponent - 1) -
        exponent * (((verticalDepth index : ℝ) - exponent * horizontalDepth index) *
          (ratios index) ^ ((verticalDepth index : ℝ) - exponent * horizontalDepth index - 1) *
          centeredTailFactor index (fun position => (digits index position).2) (ratios index) +
          (ratios index) ^ ((verticalDepth index : ℝ) - exponent * horizontalDepth index) *
            deriv (centeredTailFactor index (fun position => (digits index position).2)) (ratios index)) +
        centeredRemainderFirst exponent (horizontalDepth index) (verticalDepth index) index
          (fun position => (digits index position).2) (ratios index)) := by
    filter_upwards [hsmall, hhorizontalPositive] with index hsmall hhorizontalPositive
    have hpositive := hlower.trans_le (hratios index).1
    apply centeredNormalizedResidual_deriv exponent (horizontalDepth index) (verticalDepth index) index
      (digits index) hpositive ((hratios index).2.trans_lt hless) hhorizontalPositive
    exact ((pow_le_pow_left₀ hpositive.le (hratios index).2 _).trans
      (pow_le_pow_of_le_one (hlower.le.trans hinterval) hless.le (hdepth index))).trans_lt hsmall
  simpa only [zero_mul, mul_zero, Real.one_rpow, mul_one, add_zero, zero_add,
    zero_sub, neg_mul, mul_assoc] using hlimit.congr' hidentity.symm

end LambdaCantor.AE
