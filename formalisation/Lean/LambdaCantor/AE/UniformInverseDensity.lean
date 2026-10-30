import LambdaCantor.AE.AddressPairSecondDerivative
import LambdaCantor.AE.AddressPairExtendedDensity
import LambdaCantor.AE.ScaledCutoff
import LambdaCantor.AE.PairAnnulusScale

open Set
open scoped ContDiff

namespace LambdaCantor.AE

/-- Uniform quantitative regularity of the actual inverse density with the
constructed cutoff. Every residual and cutoff estimate used here is proved
in preceding modules. Only the smooth compactly supported parameter test
function is supplied by the caller. -/
theorem addressPairInverseDensity_uniform_estimates
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff) :
    ∃ epsilon constant : ℝ, 0 < epsilon ∧ 0 < constant ∧
      ∀ (first second third fourth : ℕ → Bool) (depth : ℕ),
        (∀ index < depth, pairDigitDifference first second third fourth index = 0) →
        0 < pairDigitDifference first second third fourth depth →
        (∀ ratio ∈ Ioo lower upper,
          |addressPairDifference first second third fourth ratio| <
            epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) →
          deriv (addressPairDifference first second third fourth) ratio < 0) ∧
        ∀ value ∈ addressPairDifference first second third fourth ''
          addressPairBand first second third fourth lower upper
            (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)),
          DifferentiableAt ℝ
            (addressPairInverseDensity first second third fourth lower upper
              (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) parameterCutoff
              (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)))) value ∧
          |deriv (addressPairInverseDensity first second third fourth lower upper
            (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) parameterCutoff
            (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)))) value| ≤
            constant * ((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth := by
  obtain ⟨epsilon, margin, hepsilon, hmargin, htransverse⟩ :=
    addressPairDifference_uniform_transversality hlower horder hupper
  obtain ⟨secondBound, hsecondBound, hsecondEstimate⟩ :=
    addressPairDifference_uniform_secondDerivative_bound hlower horder (by linarith : upper < 1)
  obtain ⟨cutoffBound, hcutoffBound, hcutoffEstimate⟩ := exists_nearBandCutoff_derivative_bound
  obtain ⟨parameterBound, hparameterBound⟩ := hcompact.exists_bound_of_continuous hsmooth.continuous
  obtain ⟨parameterDerivativeBound, hparameterDerivativeBound⟩ :=
    hcompact.deriv.exists_bound_of_continuous (hsmooth.continuous_deriv le_rfl)
  have hparameterPositive : 0 < max parameterBound 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hparameterDerivativePositive : 0 < max parameterDerivativeBound 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨epsilon,
    max parameterDerivativeBound 1 / margin ^ 2 +
      max parameterBound 1 * cutoffBound / (epsilon * margin) +
      max parameterBound 1 * secondBound / margin ^ 3,
    hepsilon, by positivity, ?_⟩
  intro first second third fourth depth hprefix hdigit
  have hnonzero := ne_of_gt hdigit
  have hthreshold : 0 < epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) := by positivity
  have hscaledMargin : 0 < margin * lower ^ depth := by positivity
  have hdiff : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio := by
    intro ratio hratio
    exact (hasDerivAt_addressPairDifference first second third fourth depth hprefix hnonzero
      (hlower.trans hratio.1) (by linarith [hratio.2] : ratio < 1)).differentiableAt
  have hnegativeBound : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| <
        epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) →
      deriv (addressPairDifference first second third fourth) ratio ≤ -(margin * lower ^ depth) := by
    intro ratio hratio hsmall
    simpa only [neg_mul] using
      htransverse first second third fourth depth hprefix hdigit ratio ⟨hratio.1.le, hratio.2.le⟩ hsmall
  have hnegative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| <
        epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) →
      deriv (addressPairDifference first second third fourth) ratio < 0 := by
    intro ratio hratio hsmall
    exact (hnegativeBound ratio hratio hsmall).trans_lt (neg_neg_of_pos hscaledMargin)
  refine ⟨hnegative, ?_⟩
  intro value hvalue
  have hopen := isOpen_addressPairBand_image first second third fourth hthreshold hdiff hnegative
  have hinterior : value ∈ interior (addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper
        (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))) := by
    rwa [hopen.interior_eq]
  have hmembership := addressPairInverse_mem_and_right_inverse first second third fourth lower upper
    (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) hvalue
  have hparameterDiff := hsmooth.differentiable_one
    (addressPairInverse first second third fourth lower upper
      (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) value)
  have hcutoffDiff := ((contDiff_nearBandCutoff
    (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))).differentiable (by simp)) value
  have hsecondDiff := (hasDerivAt_deriv_addressPairDifference first second third fourth depth hprefix hnonzero
    (hlower.trans hmembership.1.1.1) (by linarith [hmembership.1.1.2] :
      addressPairInverse first second third fourth lower upper
        (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) value < 1)).differentiableAt
  refine ⟨(hasDerivAt_addressPairInverseDensity first second third fourth parameterCutoff
    (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))) hthreshold hscaledMargin
    hdiff hnegativeBound hinterior hparameterDiff hcutoffDiff hsecondDiff).differentiableAt, ?_⟩
  have hbound := deriv_addressPairInverseDensity_bound first second third fourth parameterCutoff
    (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))) hthreshold hscaledMargin
    hdiff hnegativeBound hinterior hparameterDiff hcutoffDiff hsecondDiff
    ((show |parameterCutoff (addressPairInverse first second third fourth lower upper
      (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) value)| ≤ parameterBound by
      simpa only [Real.norm_eq_abs] using hparameterBound _).trans (le_max_left parameterBound 1))
    ((show |deriv parameterCutoff (addressPairInverse first second third fourth lower upper
      (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) value)| ≤ parameterDerivativeBound by
      simpa only [Real.norm_eq_abs] using hparameterDerivativeBound _).trans (le_max_left parameterDerivativeBound 1))
    (show |nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) value| ≤ 1 by
      rw [abs_of_nonneg (nearBandCutoff_nonneg _ _)]; exact nearBandCutoff_le_one _ _)
    (hcutoffEstimate _ hthreshold value)
    (hsecondEstimate first second third fourth depth hprefix hnonzero _
      ⟨hmembership.1.1.1.le, hmembership.1.1.2.le⟩)
  simp only [mul_one] at hbound
  exact hbound.trans (inverseDensity_firstDifference_scale depth hlower horder hepsilon hmargin
    hparameterPositive.le hparameterDerivativePositive.le hcutoffBound.le hsecondBound.le)

end LambdaCantor.AE
