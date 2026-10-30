import LambdaCantor.First.RealNormalizationBounds
import LambdaCantor.First.LeadingRealTails

noncomputable section
namespace LambdaCantor

def realNormalizedResidual (exponent : ℝ) (leftDepth rightDepth padding : ℕ)
    (left right : ℕ → Bool) (ratio : ℝ) : ℝ :=
  firstRootResidual exponent leftDepth rightDepth padding left right ratio /
    ratio ^ (exponent * (leftDepth : ℝ))

theorem realNormalizedResidual_decomposition {ratio exponent : ℝ}
    (hpositive : 0 < ratio) (hlt : ratio < 1) (leftDepth rightDepth padding : ℕ)
    (hpadding : 1 ≤ padding) (left right : ℕ → Bool) :
    realNormalizedResidual exponent leftDepth rightDepth padding left right ratio =
      firstRootAmplitude padding left ratio ^ exponent -
        exponent * ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) +
        exponent * (ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) *
          (ratio ^ padding * address ratio right)) +
        realNormalizationError exponent ((rightDepth : ℝ) - exponent * (leftDepth : ℝ))
          rightDepth padding right ratio := by
  have hamplitude : 0 ≤ firstRootAmplitude padding left ratio := by
    have := address_nonnegative hpositive.le hlt left
    dsimp [firstRootAmplitude]
    exact (add_pos_of_pos_of_nonneg (sub_pos.mpr hlt) (by positivity)).le
  have htail := (realRootTail_bounds hpositive hlt hpadding right).1
  have hidentity := normalized_real_residual_quotient (exponent := exponent)
    hpositive hamplitude htail leftDepth rightDepth
  have hy : 1 - ratio ^ rightDepth * realRootTail padding right ratio =
      firstRootY rightDepth padding right ratio := by
    dsimp [realRootTail, firstRootY]
    rw [pow_add]
    ring
  rw [hy] at hidentity
  change realNormalizedResidual exponent leftDepth rightDepth padding left right ratio -
      (firstRootAmplitude padding left ratio ^ exponent -
        exponent * ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) *
          realRootTail padding right ratio) =
      realNormalizationError exponent ((rightDepth : ℝ) - exponent * (leftDepth : ℝ))
        rightDepth padding right ratio at hidentity
  dsimp [realRootTail] at hidentity
  nlinarith only [hidentity]

theorem realNormalizedResidual_derivative_decomposition {ratio exponent : ℝ}
    (hpositive : 0 < ratio) (hlt : ratio < 1) (leftDepth rightDepth padding : ℕ)
    (hpadding : 1 ≤ padding) (hsmall : ratio ^ rightDepth ≤ (1 / 2 : ℝ))
    (left right : ℕ → Bool) :
    deriv (realNormalizedResidual exponent leftDepth rightDepth padding left right) ratio =
      deriv (fun parameter => firstRootAmplitude padding left parameter ^ exponent) ratio -
        exponent * (((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) *
          ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ) - 1)) +
        exponent * deriv (fun parameter : ℝ =>
          parameter ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) *
            (parameter ^ padding * address parameter right)) ratio +
        deriv (realNormalizationError exponent ((rightDepth : ℝ) - exponent * (leftDepth : ℝ))
          rightDepth padding right) ratio := by
  have htail := realRootTail_bounds hpositive hlt hpadding right
  have hscale : ratio ^ rightDepth * realRootTail padding right ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    ⟨mul_pos (pow_pos hpositive _) htail.1,
      (mul_le_of_le_one_right (pow_nonneg hpositive.le _) htail.2).trans hsmall⟩
  have hphaseD : HasDerivAt (fun parameter : ℝ =>
      parameter ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)))
      (((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) *
        ratio ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ) - 1)) ratio := by
    simpa using (hasDerivAt_id ratio).rpow_const (p := ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)))
      (Or.inl hpositive.ne')
  have htailD := hasDerivAt_realRootTail hpositive hlt padding right
  have herrorD := ((hphaseD.mul htailD).mul
    ((differentiableAt_rpowRemainderQuotient exponent hscale).hasDerivAt.comp ratio
      (((hasDerivAt_id ratio).pow rightDepth).mul htailD))).differentiableAt.hasDerivAt
  have hcorrectionD := (hphaseD.mul (hasDerivAt_scaled_address hpositive hlt padding right)).differentiableAt.hasDerivAt
  have hamplitude : 0 < firstRootAmplitude padding left ratio := by
    have := address_nonnegative hpositive.le hlt left
    dsimp [firstRootAmplitude]
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr hlt) (by positivity)
  have hleadingD := ((((hasDerivAt_const ratio (1 : ℝ)).sub (hasDerivAt_id ratio)).add
    (hasDerivAt_scaled_address hpositive hlt padding left)).rpow_const
      (p := exponent) (Or.inl hamplitude.ne')).differentiableAt.hasDerivAt
  have hsum := (((hleadingD.sub (hphaseD.const_mul exponent)).add
    (hcorrectionD.const_mul exponent)).add herrorD).deriv
  have hequal : realNormalizedResidual exponent leftDepth rightDepth padding left right =ᶠ[nhds ratio]
      (fun parameter => firstRootAmplitude padding left parameter ^ exponent -
        exponent * parameter ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) +
        exponent * (parameter ^ ((rightDepth : ℝ) - exponent * (leftDepth : ℝ)) *
          (parameter ^ padding * address parameter right)) +
        realNormalizationError exponent ((rightDepth : ℝ) - exponent * (leftDepth : ℝ))
          rightDepth padding right parameter) := by
    filter_upwards [Ioo_mem_nhds hpositive hlt] with parameter hparameter
    exact realNormalizedResidual_decomposition hparameter.1 hparameter.2
      leftDepth rightDepth padding hpadding left right
  rw [hequal.deriv_eq]
  exact hsum

end LambdaCantor


