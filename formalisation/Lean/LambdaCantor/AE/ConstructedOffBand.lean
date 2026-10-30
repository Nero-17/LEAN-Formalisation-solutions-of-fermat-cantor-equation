import LambdaCantor.AE.PairAnnulusIntegrability
import LambdaCantor.AE.PairAnnulusScale

open MeasureTheory

namespace LambdaCantor.AE

/-- The constructed complementary cutoff gives the exact off-band
contribution at the same first-difference scale as the inverse density. -/
theorem addressPairAnnulus_constructed_off_bound
    (first second third fourth : ℕ → Bool) (depth : ℕ)
    (parameterCutoff kernel : ℝ → ℝ) {frequency epsilon lower upper kernelBound secondKernelBound : ℝ}
    (hfrequency : 0 < frequency) (hepsilon : 0 < epsilon) (hlower : 0 < lower) (horder : lower ≤ upper)
    (hcutoff : Integrable parameterCutoff volume) (hkernelContinuous : Continuous kernel)
    (hkernelBound : ∀ point, |kernel point| ≤ kernelBound)
    (hschwartz : ∀ point, |point| ^ 2 * |kernel point| ≤ secondKernelBound) :
    |addressPairAnnulus (fun ratio => parameterCutoff ratio *
      (1 - nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))
        (addressPairDifference first second third fourth ratio))) kernel frequency first second third fourth| ≤
      ((16 * secondKernelBound / epsilon ^ 2) * ∫ ratio, |parameterCutoff ratio|) *
        ((depth + 1 : ℕ) : ℝ) ^ 2 / frequency * (upper / lower ^ 3) ^ depth := by
  have hthreshold : 0 < epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) := by positivity
  have hsecondNonneg : 0 ≤ secondKernelBound := by simpa using hschwartz 0
  have hcutoffs := integrable_addressPair_near_and_off_cutoffs first second third fourth parameterCutoff
    (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) hcutoff
  have hbound := addressPairAnnulus_off_firstDifference_band_bound
    (fun ratio => parameterCutoff ratio *
      (1 - nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))
        (addressPairDifference first second third fourth ratio))) kernel
    first second third fourth depth hfrequency (by positivity : 0 < epsilon / 4) hlower hschwartz
    (fun ratio hnonzero => by
      have hcomplement := (mul_ne_zero_iff.mp hnonzero).2
      have hseparation := nearBandCutoff_complement_nonzero_imp hthreshold hcomplement
      calc
        (epsilon / 4) * lower ^ depth / ((depth + 1 : ℕ) : ℝ) =
            (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) / 4 := by ring
        _ ≤ _ := hseparation.le)
    hcutoffs.2
    (integrable_addressPairAnnulus_integrand first second third fourth _ kernel frequency hcutoffs.2
      hkernelContinuous hkernelBound)
  have hL1 := addressPair_off_cutoff_L1_bound first second third fourth parameterCutoff
    (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ)) hcutoff
  have hL1nonneg : 0 ≤ ∫ ratio, |parameterCutoff ratio| := integral_nonneg (fun _ => abs_nonneg _)
  calc
    _ ≤ (secondKernelBound * ((depth + 1 : ℕ) : ℝ) ^ 2 /
        (frequency * (epsilon / 4) ^ 2 * lower ^ (2 * depth))) *
        (∫ ratio, |parameterCutoff ratio *
          (1 - nearBandCutoff (epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))
            (addressPairDifference first second third fourth ratio))|) := hbound
    _ ≤ (secondKernelBound * ((depth + 1 : ℕ) : ℝ) ^ 2 /
        (frequency * (epsilon / 4) ^ 2 * lower ^ (2 * depth))) *
        (∫ ratio, |parameterCutoff ratio|) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = ((16 * secondKernelBound / epsilon ^ 2) * ∫ ratio, |parameterCutoff ratio|) *
        ((depth + 1 : ℕ) : ℝ) ^ 2 / frequency * (1 / (lower ^ depth) ^ 2) := by
      rw [show lower ^ (2 * depth) = (lower ^ depth) ^ 2 by rw [Nat.mul_comm, pow_mul]]
      field_simp [ne_of_gt hfrequency, ne_of_gt hepsilon, ne_of_gt hlower]
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inverse_square_le_firstDifference_scale depth hlower horder)
      (by positivity)

end LambdaCantor.AE
