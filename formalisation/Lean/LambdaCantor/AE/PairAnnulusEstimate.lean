import LambdaCantor.AE.UniformInverseDensity
import LambdaCantor.AE.ConstructedOffBand

open Set MeasureTheory Filter

namespace LambdaCantor.AE

/-- The pair-annulus estimate for actual address pairs with positive leading
digit difference. The hypotheses on the fixed kernel are its elementary
Schwartz consequences, not an assumed pairwise integral estimate. All
cutoffs, inverse densities, change of variables, and depth dependence are
constructed or proved in the preceding chain. -/
theorem addressPairAnnulus_uniform_bound_positive_leading
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2)
    (parameterCutoff kernel : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hparameterSupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hkernelContinuous : Continuous kernel) (hkernel : Integrable kernel volume)
    (hmoment : Integrable (fun point => |point| * |kernel point|) volume)
    (hzero : ∫ point, kernel point = 0)
    {kernelBound secondKernelBound : ℝ}
    (hkernelBound : ∀ point, |kernel point| ≤ kernelBound)
    (hschwartz : ∀ point, |point| ^ 2 * |kernel point| ≤ secondKernelBound) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (first second third fourth : ℕ → Bool) (depth : ℕ),
        (∀ index < depth, pairDigitDifference first second third fourth index = 0) →
        0 < pairDigitDifference first second third fourth depth →
        ∀ frequency : ℝ, 0 < frequency →
          |addressPairAnnulus parameterCutoff kernel frequency first second third fourth| ≤
            constant * min frequency
              ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth) := by
  obtain ⟨epsilon, inverseConstant, hepsilon, hinverseConstant, hinverseEstimate⟩ :=
    addressPairInverseDensity_uniform_estimates hlower horder hupper parameterCutoff hsmooth hcompact
  have hparameterIntegrable : Integrable parameterCutoff volume :=
    hsmooth.continuous.integrable_of_hasCompactSupport hcompact
  have hkernelNonneg : 0 ≤ kernelBound := (abs_nonneg (kernel 0)).trans (hkernelBound 0)
  have hsecondNonneg : 0 ≤ secondKernelBound := by simpa using hschwartz 0
  have hmomentNonneg : 0 ≤ ∫ point, |point| * |kernel point| := integral_nonneg (fun _ => by positivity)
  have hparameterL1Nonneg : 0 ≤ ∫ ratio, |parameterCutoff ratio| := integral_nonneg (fun _ => abs_nonneg _)
  let totalConstant : ℝ := 1 + kernelBound * (∫ ratio, |parameterCutoff ratio|) +
    inverseConstant * (∫ point, |point| * |kernel point|) +
    (16 * secondKernelBound / epsilon ^ 2) * (∫ ratio, |parameterCutoff ratio|)
  have htotalPositive : 0 < totalConstant := by unfold totalConstant; positivity
  refine ⟨totalConstant, htotalPositive, ?_⟩
  intro first second third fourth depth hprefix hdigit frequency hfrequency
  have hnonzero := ne_of_gt hdigit
  have hthreshold : 0 < epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) := by positivity
  have hscale : 0 ≤ inverseConstant * ((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth := by
    have hupperpos := hlower.trans_le horder
    positivity
  obtain ⟨hnegative, hlocal⟩ := hinverseEstimate first second third fourth depth hprefix hdigit
  have hdiff : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio := by
    intro ratio hratio
    exact (hasDerivAt_addressPairDifference first second third fourth depth hprefix hnonzero
      (hlower.trans hratio.1) (by linarith [hratio.2] : ratio < 1)).differentiableAt
  have hsupport := addressPairExtendedDensity_support first second third fourth parameterCutoff
    (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)))
    hdiff hcompact hparameterSupport (tsupport_nearBandCutoff_subset hthreshold)
  have hlipschitz := lipschitzWith_addressPairExtendedDensity first second third fourth parameterCutoff
    (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)))
    ⟨inverseConstant * ((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth, hscale⟩
    (isOpen_addressPairBand_image first second third fourth hthreshold hdiff hnegative)
    hsupport.2 hlocal
  obtain ⟨densityBound, hdensityBound⟩ := hsupport.1.exists_bound_of_continuous hlipschitz.continuous
  have hproduct : Integrable (fun point => kernel point *
      addressPairExtendedDensity first second third fourth lower upper
        (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) parameterCutoff
        (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))) (point / frequency)) volume := by
    apply hkernel.mul_bdd (hlipschitz.continuous.comp (continuous_id.div_const frequency)).aestronglyMeasurable
    exact Eventually.of_forall (fun point => hdensityBound (point / frequency))
  have hnear := addressPairAnnulus_near_band_bound first second third fourth parameterCutoff
    (nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))) kernel
    ⟨inverseConstant * ((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth, hscale⟩
    hthreshold hfrequency hdiff hnegative hcompact hparameterSupport
    (tsupport_nearBandCutoff_subset hthreshold) hlocal hkernel hproduct hmoment hzero
  change _ ≤
    (inverseConstant * ((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth / frequency) *
      (∫ point, |point| * |kernel point|) at hnear
  have hoff := addressPairAnnulus_constructed_off_bound first second third fourth depth parameterCutoff kernel
    hfrequency hepsilon hlower horder hparameterIntegrable hkernelContinuous hkernelBound hschwartz
  have hsplit := addressPairAnnulus_split_cutoff first second third fourth parameterCutoff kernel
    (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) frequency hparameterIntegrable hkernelContinuous hkernelBound
  have hdecay : |addressPairAnnulus parameterCutoff kernel frequency first second third fourth| ≤
      totalConstant * ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth) := by
    calc
      _ = |addressPairAnnulus (fun ratio => parameterCutoff ratio *
            nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))
              (addressPairDifference first second third fourth ratio)) kernel frequency first second third fourth +
          addressPairAnnulus (fun ratio => parameterCutoff ratio *
            (1 - nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))
              (addressPairDifference first second third fourth ratio))) kernel frequency first second third fourth| :=
        congrArg abs hsplit
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hnear hoff)
      _ = (inverseConstant * (∫ point, |point| * |kernel point|) +
          (16 * secondKernelBound / epsilon ^ 2) * (∫ ratio, |parameterCutoff ratio|)) *
          ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by unfold totalConstant; nlinarith [mul_nonneg hkernelNonneg hparameterL1Nonneg])
        (by have hupperpos := hlower.trans_le horder; positivity)
  have htrivial := addressPairAnnulus_trivial_bound parameterCutoff kernel first second third fourth
    hfrequency.le hkernelBound hparameterIntegrable
    (integrable_addressPairAnnulus_integrand first second third fourth parameterCutoff kernel frequency
      hparameterIntegrable hkernelContinuous hkernelBound)
  have hlinear : |addressPairAnnulus parameterCutoff kernel frequency first second third fourth| ≤
      totalConstant * frequency := by
    apply htrivial.trans
    have hconstant : kernelBound * (∫ ratio, |parameterCutoff ratio|) ≤ totalConstant := by
      unfold totalConstant
      nlinarith [mul_nonneg hinverseConstant.le hmomentNonneg,
        mul_nonneg (show 0 ≤ 16 * secondKernelBound / epsilon ^ 2 by positivity) hparameterL1Nonneg]
    nlinarith [mul_le_mul_of_nonneg_right hconstant hfrequency.le]
  rw [mul_min_of_nonneg _ _ htotalPositive.le]
  exact le_min hlinear hdecay

theorem addressPairDifference_swap (first second third fourth : ℕ → Bool) (ratio : ℝ) :
    addressPairDifference third fourth first second ratio =
      -addressPairDifference first second third fourth ratio := by
  unfold addressPairDifference
  ring

theorem pairDigitDifference_swap (first second third fourth : ℕ → Bool) (index : ℕ) :
    pairDigitDifference third fourth first second index =
      -pairDigitDifference first second third fourth index := by
  unfold pairDigitDifference
  ring

theorem addressPairAnnulus_swap (first second third fourth : ℕ → Bool)
    (parameterCutoff kernel : ℝ → ℝ) (frequency : ℝ) (heven : ∀ point, kernel (-point) = kernel point) :
    addressPairAnnulus parameterCutoff kernel frequency third fourth first second =
      addressPairAnnulus parameterCutoff kernel frequency first second third fourth := by
  unfold addressPairAnnulus
  apply integral_congr_ae
  exact Eventually.of_forall (fun ratio => by
    change parameterCutoff ratio * frequency *
        kernel (frequency * addressPairDifference third fourth first second ratio) =
      parameterCutoff ratio * frequency *
        kernel (frequency * addressPairDifference first second third fourth ratio)
    rw [addressPairDifference_swap, mul_neg, heven])

/-- Full real-even-kernel version of (pair-annulus), for every nonzero
first difference. An even real frequency cutoff gives this kernel symmetry.
The polynomial depth loss is explicitly degree two. -/
theorem addressPairAnnulus_uniform_bound
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2)
    (parameterCutoff kernel : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hparameterSupport : tsupport parameterCutoff ⊆ Ioo lower upper)
    (hkernelContinuous : Continuous kernel) (hkernel : Integrable kernel volume)
    (hmoment : Integrable (fun point => |point| * |kernel point|) volume)
    (hzero : ∫ point, kernel point = 0) (heven : ∀ point, kernel (-point) = kernel point)
    {kernelBound secondKernelBound : ℝ}
    (hkernelBound : ∀ point, |kernel point| ≤ kernelBound)
    (hschwartz : ∀ point, |point| ^ 2 * |kernel point| ≤ secondKernelBound) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (first second third fourth : ℕ → Bool) (depth : ℕ),
        (∀ index < depth, pairDigitDifference first second third fourth index = 0) →
        pairDigitDifference first second third fourth depth ≠ 0 →
        ∀ frequency : ℝ, 0 < frequency →
          |addressPairAnnulus parameterCutoff kernel frequency first second third fourth| ≤
            constant * min frequency
              ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth) := by
  obtain ⟨constant, hconstant, hestimate⟩ := addressPairAnnulus_uniform_bound_positive_leading
    hlower horder hupper parameterCutoff kernel hsmooth hcompact hparameterSupport hkernelContinuous
    hkernel hmoment hzero hkernelBound hschwartz
  refine ⟨constant, hconstant, ?_⟩
  intro first second third fourth depth hprefix hnonzero frequency hfrequency
  rcases lt_or_gt_of_ne hnonzero with hnegative | hpositive
  · have hbound := hestimate third fourth first second depth
      (fun index hindex => by rw [pairDigitDifference_swap, hprefix index hindex, neg_zero])
      (by rw [pairDigitDifference_swap]; exact neg_pos.mpr hnegative) frequency hfrequency
    rw [addressPairAnnulus_swap first second third fourth parameterCutoff kernel frequency heven] at hbound
    exact hbound
  · exact hestimate first second third fourth depth hprefix hpositive frequency hfrequency

end LambdaCantor.AE
