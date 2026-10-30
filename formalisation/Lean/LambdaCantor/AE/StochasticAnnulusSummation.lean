import LambdaCantor.AE.FirstDifferenceIntegration

noncomputable section
open Set MeasureTheory

namespace LambdaCantor.AE

def expectedAbsoluteAnnulus (parameterCutoff : ℝ → ℝ) (frequency : ℝ) : ℝ :=
  ∫ sample : ℕ → FourDigits,
    |addressPairAnnulus parameterCutoff annularKernel frequency
      (fun index => sample index 0) (fun index => sample index 1)
      (fun index => sample index 2) (fun index => sample index 3)| ∂fourAddressMeasure

theorem expectedAbsoluteAnnulus_nonneg (parameterCutoff : ℝ → ℝ) (frequency : ℝ) :
    0 ≤ expectedAbsoluteAnnulus parameterCutoff frequency :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem summable_firstDifference_majorant {growth frequency : ℝ}
    (hgrowth : 0 ≤ growth) (hfrequency : 0 < frequency) :
    Summable (fun depth : ℕ => (3 / 8 : ℝ) ^ depth * min frequency
      ((((depth + 1 : ℕ) : ℝ) ^ 2 * growth ^ depth) / frequency)) := by
  apply Summable.of_nonneg_of_le _ _
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 8)
      (by norm_num : (3 / 8 : ℝ) < 1)).mul_right frequency)
  · intro depth
    positivity
  · intro depth
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (pow_nonneg (by norm_num) _)

/-- The actual stochastic sum, obtained by integrating the disjoint first-difference cells. -/
theorem expectedAbsoluteAnnulus_bound
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ frequency : ℝ, 0 < frequency →
      expectedAbsoluteAnnulus parameterCutoff frequency ≤ constant *
        ∑' depth : ℕ, (3 / 8 : ℝ) ^ depth * min frequency
          ((((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth) / frequency) := by
  obtain ⟨constant, hconstant, hcell⟩ := actual_pair_annulus_depth_integral_bound
    hlower horder hupper parameterCutoff hsmooth hcompact hsupport
  refine ⟨constant, hconstant, ?_⟩
  intro frequency hfrequency
  have hintegrable := (integrable_actualPairAnnulus parameterCutoff frequency
    (hsmooth.continuous.integrable_of_hasCompactSupport hcompact)).norm
  have hcells := (hasSum_integral_iUnion measurableSet_firstPairDifference
    firstPairDifference_pairwiseDisjoint hintegrable.integrableOn).summable
  have hgrowth : 0 ≤ upper / lower ^ 3 := div_nonneg (hlower.le.trans horder) (by positivity)
  have hmajorant := (summable_firstDifference_majorant hgrowth hfrequency).mul_left constant
  unfold expectedAbsoluteAnnulus
  have hpartition := integral_firstPairDifference_partition hintegrable
  simp only [Real.norm_eq_abs] at hpartition hcells
  rw [hpartition]
  simpa only [tsum_mul_left] using
    Summable.tsum_le_tsum (fun depth => hcell depth frequency hfrequency) hcells hmajorant

/-- The actual expected absolute annular integrals are dyadically summable throughout the
manuscript's strict logarithmic range. The only numerical summation input is the verified
AnnulusSummation theorem; the stochastic bounds above are derived for the constructed kernel. -/
theorem summable_actual_weighted_annuli
    {lower upper regularity : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper)
    (hupper : upper < 1 / 2) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity <
      2 * Real.log (8 / 3 : ℝ) / Real.log (upper / lower ^ 3) - 1)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper) :
    Summable (fun scale : ℕ => ((2 : ℝ) ^ scale) ^ (2 * regularity) *
      expectedAbsoluteAnnulus parameterCutoff ((2 : ℝ) ^ scale)) := by
  obtain ⟨constant, hconstant, hbound⟩ := expectedAbsoluteAnnulus_bound
    hlower horder hupper parameterCutoff hsmooth hcompact hsupport
  have hgrowth : (8 / 3 : ℝ) < upper / lower ^ 3 := by
    have hfour := annulus_growth_gt_four hlower horder hupper
    linarith
  have hmajorant := (summable_weighted_annulus_series 2 hgrowth hregularity hrange).mul_left constant
  apply Summable.of_nonneg_of_le _ _ hmajorant
  · intro scale
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (expectedAbsoluteAnnulus_nonneg _ _)
  · intro scale
    have hestimate := mul_le_mul_of_nonneg_left
      (hbound ((2 : ℝ) ^ scale) (by positivity))
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ scale) (2 * regularity))
    simpa only [mul_left_comm] using hestimate

end LambdaCantor.AE
