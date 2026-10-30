import LambdaCantor.AE.AnnularFourierIntegrability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

namespace LambdaCantor.AE

/-- The real-even projection of the actual Fourier kernel of our annular cutoff. -/
def annularKernel (value : ℝ) : ℝ :=
  ((𝓕 complexAnnularCutoff value).re + (𝓕 complexAnnularCutoff (-value)).re) / 2

theorem continuous_annularKernel : Continuous annularKernel := by
  refine (((Complex.continuous_re.comp continuous_annularCutoff_fourier).add
    (Complex.continuous_re.comp (continuous_annularCutoff_fourier.comp continuous_neg))).div_const 2).congr ?_
  intro value
  rfl

theorem annularKernel_even (value : ℝ) : annularKernel (-value) = annularKernel value := by
  simp only [annularKernel, neg_neg, add_comm]

theorem abs_annularKernel_le (value : ℝ) :
    |annularKernel value| ≤
      (‖𝓕 complexAnnularCutoff value‖ + ‖𝓕 complexAnnularCutoff (-value)‖) / 2 := by
  unfold annularKernel
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (abs_add_le _ _).trans (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))

theorem annularKernel_polynomial_bound (power : ℕ) :
    ∃ constant : ℝ, ∀ value, |value| ^ power * |annularKernel value| ≤ constant := by
  refine ⟨2 ^ power * ∑ derivative ∈ Finset.range 1 ×ˢ Finset.range (power + 1),
    ∫ value : ℝ, ‖value‖ ^ derivative.1 *
      ‖iteratedFDeriv ℝ derivative.2 complexAnnularCutoff value‖, ?_⟩
  intro value
  have hpositive := annularCutoff_fourier_decay power value
  have hnegative := annularCutoff_fourier_decay power (-value)
  simp only [norm_neg, Real.norm_eq_abs] at hpositive hnegative
  have hkernel := mul_le_mul_of_nonneg_left (abs_annularKernel_le value)
    (pow_nonneg (abs_nonneg value) power)
  simp only [Real.norm_eq_abs]
  nlinarith

theorem integrable_annularKernel_moment (power : ℕ) :
    Integrable (fun value : ℝ => |value| ^ power * |annularKernel value|) := by
  obtain ⟨constantZero, hzero⟩ := annularKernel_polynomial_bound power
  obtain ⟨constantTwo, htwo⟩ := annularKernel_polynomial_bound (power + 2)
  refine integrable_of_bounded_and_quadratic_decay
    (function := fun value : ℝ => |value| ^ power * |annularKernel value|)
    (constantZero := constantZero) (constantTwo := constantTwo) ?_ ?_ ?_
  · exact (((continuous_abs.pow power).mul continuous_annularKernel.abs).congr
      (fun value => rfl)).aestronglyMeasurable
  · intro value
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs] using hzero value
  · intro value
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, ← mul_assoc,
      ← pow_add, Nat.add_comm 2 power] using htwo value

theorem integrable_annularKernel : Integrable annularKernel := by
  have habs : Integrable (fun value => |annularKernel value|) := by
    simpa only [pow_zero, one_mul] using integrable_annularKernel_moment 0
  exact habs.mono continuous_annularKernel.aestronglyMeasurable
    (Eventually.of_forall (fun _ => by simp [Real.norm_eq_abs]))

theorem integral_annularKernel : (∫ value, annularKernel value) = 0 := by
  have hforward : (∫ value : ℝ, 𝓕 complexAnnularCutoff value) = 0 := by
    have hinverse := integral_annularCutoff_inverseFourier
    simp_rw [Real.fourierInv_eq_fourier_neg] at hinverse
    rwa [integral_neg_eq_self (𝓕 complexAnnularCutoff) volume] at hinverse
  have hreal : Integrable (fun value => (𝓕 complexAnnularCutoff value).re) :=
    integrable_annularCutoff_fourier.re
  have hnegative : Integrable (fun value => (𝓕 complexAnnularCutoff (-value)).re) := by
    simpa only [neg_one_mul] using hreal.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have hnegative_integral :
      (∫ value : ℝ, (𝓕 complexAnnularCutoff (-value)).re) =
        ∫ value : ℝ, (𝓕 complexAnnularCutoff value).re :=
    integral_neg_eq_self (fun value : ℝ => (𝓕 complexAnnularCutoff value).re) volume
  have hreal_integral : (∫ value : ℝ, (𝓕 complexAnnularCutoff value).re) = 0 := by
    calc
      _ = (∫ value : ℝ, 𝓕 complexAnnularCutoff value).re := by
        simpa only [Complex.reCLM_apply] using
          Complex.reCLM.integral_comp_comm integrable_annularCutoff_fourier
      _ = 0 := by rw [hforward]; rfl
  unfold annularKernel
  rw [integral_div, integral_add hreal hnegative, hnegative_integral]
  simp only [hreal_integral, add_zero, zero_div]

/-- Every elementary kernel hypothesis in the pairwise estimate is now supplied by an
actual annular Fourier kernel, without assuming any decay or cancellation property. -/
theorem annularKernel_pairwise_hypotheses :
    Continuous annularKernel ∧ Integrable annularKernel ∧
    Integrable (fun value : ℝ => |value| * |annularKernel value|) ∧
    (∫ value, annularKernel value) = 0 ∧
    (∃ boundZero : ℝ, ∀ value, |annularKernel value| ≤ boundZero) ∧
    (∃ boundTwo : ℝ, ∀ value, |value| ^ 2 * |annularKernel value| ≤ boundTwo) := by
  refine ⟨continuous_annularKernel, integrable_annularKernel, ?_, integral_annularKernel, ?_,
    annularKernel_polynomial_bound 2⟩
  · simpa only [pow_one] using integrable_annularKernel_moment 1
  · simpa only [pow_zero, one_mul] using annularKernel_polynomial_bound 0

end LambdaCantor.AE
