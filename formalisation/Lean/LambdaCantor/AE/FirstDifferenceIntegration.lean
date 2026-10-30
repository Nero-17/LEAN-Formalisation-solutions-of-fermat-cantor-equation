import LambdaCantor.AE.ActualPairAnnulus
import LambdaCantor.AE.PairFubini
import LambdaCantor.AE.AnnulusSummation

noncomputable section
open Set MeasureTheory Filter

namespace LambdaCantor.AE

theorem measurableSet_firstPairDifference (depth : ℕ) : MeasurableSet (firstPairDifference depth) := by
  apply MeasurableSet.inter
  · exact MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => (Set.toFinite _).measurableSet)
  · exact ((Set.toFinite equalPairDigits).measurableSet.preimage (measurable_pi_apply depth)).compl

theorem integral_firstPairDifference_partition {function : (ℕ → FourDigits) → ℝ}
    (hintegrable : Integrable function fourAddressMeasure) :
    (∫ sample, function sample ∂fourAddressMeasure) =
      ∑' depth, ∫ sample in firstPairDifference depth, function sample ∂fourAddressMeasure := by
  have hfull : ∀ᵐ sample ∂fourAddressMeasure, sample ∈ ⋃ depth, firstPairDifference depth := by
    simpa only [Set.mem_iUnion] using ae_exists_firstPairDifference
  have hpartition := integral_iUnion measurableSet_firstPairDifference
    firstPairDifference_pairwiseDisjoint hintegrable.integrableOn
  rwa [Measure.restrict_eq_self_of_ae_mem hfull] at hpartition

theorem integrable_actualPairAnnulus (parameterCutoff : ℝ → ℝ) (frequency : ℝ)
    (hcutoff : Integrable parameterCutoff) :
    Integrable (fun sample : ℕ → FourDigits =>
      addressPairAnnulus parameterCutoff annularKernel frequency
        (fun index => sample index 0) (fun index => sample index 1)
        (fun index => sample index 2) (fun index => sample index 3)) fourAddressMeasure := by
  obtain ⟨bound, hbound⟩ := annularKernel_pairwise_hypotheses.2.2.2.2.1
  exact (integrable_sample_parameter_kernel parameterCutoff annularKernel frequency bound
    hcutoff continuous_annularKernel hbound).integral_prod_left

/-- The actual per-depth integral includes the geometric probability factor. -/
theorem actual_pair_annulus_depth_integral_bound
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ depth : ℕ, ∀ frequency : ℝ, 0 < frequency →
      (∫ sample in firstPairDifference depth,
        |addressPairAnnulus parameterCutoff annularKernel frequency
          (fun index => sample index 0) (fun index => sample index 1)
          (fun index => sample index 2) (fun index => sample index 3)| ∂fourAddressMeasure) ≤
        constant * ((3 / 8 : ℝ) ^ depth * min frequency
          ((((depth + 1 : ℕ) : ℝ) ^ 2 * (upper / lower ^ 3) ^ depth) / frequency)) := by
  obtain ⟨constant, hconstant, hbound⟩ := actual_pair_annulus_bound
    hlower horder hupper parameterCutoff hsmooth hcompact hsupport
  refine ⟨constant, hconstant, ?_⟩
  intro depth frequency hfrequency
  have hnonnegative : 0 ≤ min frequency
      ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth) := by
    have hupperpos := hlower.trans_le horder
    positivity
  have hmeasure : fourAddressMeasure.real (firstPairDifference depth) ≤ (3 / 8 : ℝ) ^ depth := by
    have hle := ENNReal.toReal_mono (by finiteness) (measure_firstPairDifference_le depth)
    simpa only [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofNat] using hle
  calc
    _ ≤ ∫ _ in firstPairDifference depth, constant * min frequency
        ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth)
        ∂fourAddressMeasure := by
      apply setIntegral_mono_on
        (integrable_actualPairAnnulus parameterCutoff frequency
          (hsmooth.continuous.integrable_of_hasCompactSupport hcompact)).norm.integrableOn
        (integrable_const _).integrableOn (measurableSet_firstPairDifference depth)
      exact fun sample hsample => hbound sample depth hsample frequency hfrequency
    _ = fourAddressMeasure.real (firstPairDifference depth) * (constant * min frequency
        ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth)) := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ (3 / 8 : ℝ) ^ depth * (constant * min frequency
        ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth)) :=
      mul_le_mul_of_nonneg_right hmeasure (mul_nonneg hconstant.le hnonnegative)
    _ = _ := by
      simp only [div_mul_eq_mul_div]
      ring

end LambdaCantor.AE
