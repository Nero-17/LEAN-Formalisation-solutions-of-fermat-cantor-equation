import LambdaCantor.AE.ActualAnnularKernel
import LambdaCantor.AE.PairAnnulusEstimate
import LambdaCantor.AE.PairProbability

open Set MeasureTheory

namespace LambdaCantor.AE

/-- The fully instantiated pair estimate: the kernel is the constructed annular Fourier
kernel, and the event is the actual first difference in the four-address sample space. -/
theorem actual_pair_annulus_bound
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2)
    (parameterCutoff : ℝ → ℝ) (hsmooth : ContDiff ℝ 1 parameterCutoff)
    (hcompact : HasCompactSupport parameterCutoff)
    (hsupport : tsupport parameterCutoff ⊆ Ioo lower upper) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (sample : ℕ → FourDigits) (depth : ℕ), sample ∈ firstPairDifference depth →
      ∀ frequency : ℝ, 0 < frequency →
        |addressPairAnnulus parameterCutoff annularKernel frequency
          (fun index => sample index 0) (fun index => sample index 1)
          (fun index => sample index 2) (fun index => sample index 3)| ≤
          constant * min frequency
            ((((depth + 1 : ℕ) : ℝ) ^ 2 / frequency) * (upper / lower ^ 3) ^ depth) := by
  obtain ⟨hcontinuous, hintegrable, hmoment, hzero, ⟨boundZero, hboundZero⟩,
    ⟨boundTwo, hboundTwo⟩⟩ := annularKernel_pairwise_hypotheses
  obtain ⟨constant, hconstant, hbound⟩ := addressPairAnnulus_uniform_bound
    hlower horder hupper parameterCutoff annularKernel hsmooth hcompact hsupport
    hcontinuous hintegrable hmoment hzero annularKernel_even hboundZero hboundTwo
  refine ⟨constant, hconstant, ?_⟩
  intro sample depth hsample frequency hfrequency
  have hleading := firstPairDifference_has_leading_digit hsample
  exact hbound _ _ _ _ depth hleading.1 hleading.2 frequency hfrequency

end LambdaCantor.AE
