import LambdaCantor.Basic
import LambdaCantor.AE.DifferenceSeries
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open MeasureTheory

namespace LambdaCantor.AE

/-- The actual difference between two points sampled from the self-convolution.
All four addresses use the paper's address map, including its 1-ratio factor. -/
def addressPairDifference (first second third fourth : ℕ → Bool) (ratio : ℝ) : ℝ :=
  address ratio first + address ratio second - (address ratio third + address ratio fourth)

/-- Difference of the two self-convolution digits at one position. -/
def pairDigitDifference (first second third fourth : ℕ → Bool) (index : ℕ) : ℝ :=
  (if first index then 1 else 0) + (if second index then 1 else 0) -
    ((if third index then 1 else 0) + (if fourth index then 1 else 0))

theorem abs_pairDigitDifference_le_two (first second third fourth : ℕ → Bool) (index : ℕ) :
    |pairDigitDifference first second third fourth index| ≤ 2 := by
  unfold pairDigitDifference
  split_ifs <;> norm_num

theorem one_le_abs_pairDigitDifference (first second third fourth : ℕ → Bool) (index : ℕ)
    (hnonzero : pairDigitDifference first second third fourth index ≠ 0) :
    1 ≤ |pairDigitDifference first second third fourth index| := by
  unfold pairDigitDifference at *
  split_ifs at * <;> norm_num at *

theorem addressPairDifference_eq_series (first second third fourth : ℕ → Bool)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    addressPairDifference first second third fourth ratio =
      (1 - ratio) * ∑' index, pairDigitDifference first second third fourth index * ratio ^ index := by
  have hfirst := address_summable hpos.le hlt first
  have hsecond := address_summable hpos.le hlt second
  have hthird := address_summable hpos.le hlt third
  have hfourth := address_summable hpos.le hlt fourth
  unfold addressPairDifference address
  rw [show (fun index => pairDigitDifference first second third fourth index * ratio ^ index) =
      (fun index => ((if first index then (1 : ℝ) else 0) * ratio ^ index +
        (if second index then (1 : ℝ) else 0) * ratio ^ index) -
        ((if third index then (1 : ℝ) else 0) * ratio ^ index +
        (if fourth index then (1 : ℝ) else 0) * ratio ^ index)) by
      funext index; unfold pairDigitDifference; ring]
  rw [(hfirst.add hsecond).tsum_sub (hthird.add hfourth),
    hfirst.tsum_add hsecond, hthird.tsum_add hfourth]
  ring

/-- The coefficient sequence used in the transversality lemmas, now defined
from the actual four addresses and their first unequal convolution digit. -/
def normalizedPairCoefficients (first second third fourth : ℕ → Bool)
    (depth index : ℕ) : ℝ :=
  pairDigitDifference first second third fourth (index + (depth + 1)) /
    pairDigitDifference first second third fourth depth

theorem normalizedPairCoefficients_bound (first second third fourth : ℕ → Bool) (depth : ℕ)
    (hnonzero : pairDigitDifference first second third fourth depth ≠ 0) :
    ∀ index, |normalizedPairCoefficients first second third fourth depth index| ≤ 2 := by
  intro index
  have hdenominator := one_le_abs_pairDigitDifference first second third fourth depth hnonzero
  have hnumerator := abs_pairDigitDifference_le_two first second third fourth (index + (depth + 1))
  unfold normalizedPairCoefficients
  rw [abs_div]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hdenominator)).mpr
  linarith

/-- Exact first-difference normalization for the actual self-convolution
pair. This connects the formal series transversality estimates to Q in
equation (pair-annulus). -/
theorem addressPairDifference_eq_normalized (first second third fourth : ℕ → Bool)
    (depth : ℕ) (hprefix : ∀ index < depth, pairDigitDifference first second third fourth index = 0)
    (hnonzero : pairDigitDifference first second third fourth depth ≠ 0)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    addressPairDifference first second third fourth ratio =
      pairDigitDifference first second third fourth depth * (1 - ratio) * ratio ^ depth *
        normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio := by
  have hsummable : Summable (fun index =>
      pairDigitDifference first second third fourth index * ratio ^ index) := by
    simpa using summable_bounded_polynomial_geometric
      (pairDigitDifference first second third fourth)
      (abs_pairDigitDifference_le_two first second third fourth) 0 hpos hlt
  have hprefixsum : ∑ index ∈ Finset.range depth,
      pairDigitDifference first second third fourth index * ratio ^ index = 0 := by
    apply Finset.sum_eq_zero
    intro index hindex
    rw [hprefix index (Finset.mem_range.mp hindex), zero_mul]
  have hsplit := hsummable.sum_add_tsum_nat_add (depth + 1)
  rw [Finset.sum_range_succ, hprefixsum, zero_add] at hsplit
  have htail : (∑' index, pairDigitDifference first second third fourth
      (index + (depth + 1)) * ratio ^ (index + (depth + 1))) =
      (pairDigitDifference first second third fourth depth * ratio ^ depth) *
        ∑' index, normalizedPairCoefficients first second third fourth depth index *
          ratio ^ (index + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro index
    rw [show ratio ^ (index + (depth + 1)) = ratio ^ depth * ratio ^ (index + 1) by
      rw [show index + (depth + 1) = depth + (index + 1) by omega, pow_add]]
    unfold normalizedPairCoefficients
    field_simp [hnonzero]
    <;> ring
  rw [htail] at hsplit
  rw [addressPairDifference_eq_series first second third fourth hpos hlt, ← hsplit]
  unfold normalizedDifference
  ring

/-- The parameter integral on the left side of the manuscript's pair-annulus
estimate, defined using actual address pairs rather than an abstract residual. -/
def addressPairAnnulus (parameterCutoff kernel : ℝ → ℝ) (frequency : ℝ)
    (first second third fourth : ℕ → Bool) : ℝ :=
  ∫ ratio, parameterCutoff ratio * frequency *
    kernel (frequency * addressPairDifference first second third fourth ratio)

/-- Exact replacement of the actual pair residual by its normalized series
inside the parameter kernel. The parameter cutoff is supported in the
convergence interval; no formula is asserted outside that interval. -/
theorem addressPairAnnulus_eq_normalized
    (parameterCutoff kernel : ℝ → ℝ) (frequency : ℝ)
    (first second third fourth : ℕ → Bool) (depth : ℕ)
    (hprefix : ∀ index < depth, pairDigitDifference first second third fourth index = 0)
    (hnonzero : pairDigitDifference first second third fourth depth ≠ 0)
    (hsupport : ∀ ratio, ratio ∉ Set.Ioo (0 : ℝ) 1 → parameterCutoff ratio = 0) :
    addressPairAnnulus parameterCutoff kernel frequency first second third fourth =
      ∫ ratio, parameterCutoff ratio * frequency *
        kernel (frequency * (pairDigitDifference first second third fourth depth *
          (1 - ratio) * ratio ^ depth *
            normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio)) := by
  unfold addressPairAnnulus
  apply integral_congr_ae
  filter_upwards [] with ratio
  by_cases hratio : ratio ∈ Set.Ioo (0 : ℝ) 1
  · rw [addressPairDifference_eq_normalized first second third fourth depth hprefix hnonzero
      hratio.1 hratio.2]
  · simp only [hsupport ratio hratio, zero_mul]

theorem addressPairAnnulus_trivial_bound
    (parameterCutoff kernel : ℝ → ℝ) {frequency kernelBound : ℝ}
    (first second third fourth : ℕ → Bool)
    (hfrequency : 0 ≤ frequency) (hkernel : ∀ point, |kernel point| ≤ kernelBound)
    (hcutoff : Integrable parameterCutoff volume)
    (hintegrable : Integrable (fun ratio => parameterCutoff ratio * frequency *
      kernel (frequency * addressPairDifference first second third fourth ratio)) volume) :
    |addressPairAnnulus parameterCutoff kernel frequency first second third fourth| ≤
      frequency * kernelBound * ∫ ratio, |parameterCutoff ratio| := by
  unfold addressPairAnnulus
  calc
    _ ≤ ∫ ratio, |parameterCutoff ratio * frequency *
        kernel (frequency * addressPairDifference first second third fourth ratio)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun ratio : ℝ => parameterCutoff ratio * frequency *
          kernel (frequency * addressPairDifference first second third fourth ratio)))
    _ ≤ ∫ ratio, (frequency * kernelBound) * |parameterCutoff ratio| := by
      apply integral_mono hintegrable.norm (hcutoff.norm.const_mul (frequency * kernelBound))
      intro ratio
      change |parameterCutoff ratio * frequency *
        kernel (frequency * addressPairDifference first second third fourth ratio)| ≤
          frequency * kernelBound * |parameterCutoff ratio|
      rw [abs_mul, abs_mul, abs_of_nonneg hfrequency]
      calc
        _ ≤ (|parameterCutoff ratio| * frequency) * kernelBound :=
          mul_le_mul_of_nonneg_left (hkernel _) (mul_nonneg (abs_nonneg _) hfrequency)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

/-- The off-band part of (pair-annulus) for the actual address residual.
The cutoff may already include the smooth factor 1-chi(Q); its support
condition is exactly the lower bound on |Q| outside the small-value band.
Only the order-two Schwartz seminorm is needed for this estimate. -/
theorem addressPairAnnulus_off_band_bound
    (parameterCutoff kernel : ℝ → ℝ) {frequency kernelBound threshold : ℝ}
    (first second third fourth : ℕ → Bool)
    (hfrequency : 0 < frequency) (hthreshold : 0 < threshold)
    (hschwartz : ∀ point, |point| ^ 2 * |kernel point| ≤ kernelBound)
    (hsupport : ∀ ratio, parameterCutoff ratio ≠ 0 →
      threshold ≤ |addressPairDifference first second third fourth ratio|)
    (hcutoff : Integrable parameterCutoff volume)
    (hintegrable : Integrable (fun ratio => parameterCutoff ratio * frequency *
      kernel (frequency * addressPairDifference first second third fourth ratio)) volume) :
    |addressPairAnnulus parameterCutoff kernel frequency first second third fourth| ≤
      (kernelBound / (frequency * threshold ^ 2)) * ∫ ratio, |parameterCutoff ratio| := by
  have hscaled : ∀ ratio, parameterCutoff ratio ≠ 0 →
      frequency * |kernel (frequency * addressPairDifference first second third fourth ratio)| ≤
        kernelBound / (frequency * threshold ^ 2) := by
    intro ratio hnonzero
    have hsquare : threshold ^ 2 ≤
        |addressPairDifference first second third fourth ratio| ^ 2 :=
      pow_le_pow_left₀ hthreshold.le (hsupport ratio hnonzero) 2
    have hweighted := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare (sq_nonneg frequency))
      (abs_nonneg (kernel (frequency * addressPairDifference first second third fourth ratio)))
    have hkernel := hschwartz (frequency * addressPairDifference first second third fourth ratio)
    rw [abs_mul, abs_of_pos hfrequency, mul_pow] at hkernel
    apply (le_div_iff₀ (by positivity : 0 < frequency * threshold ^ 2)).mpr
    calc
      _ = frequency ^ 2 * threshold ^ 2 *
          |kernel (frequency * addressPairDifference first second third fourth ratio)| := by ring
      _ ≤ _ := hweighted.trans hkernel
  unfold addressPairAnnulus
  calc
    _ ≤ ∫ ratio, |parameterCutoff ratio * frequency *
        kernel (frequency * addressPairDifference first second third fourth ratio)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun ratio : ℝ => parameterCutoff ratio * frequency *
          kernel (frequency * addressPairDifference first second third fourth ratio)))
    _ ≤ ∫ ratio, (kernelBound / (frequency * threshold ^ 2)) * |parameterCutoff ratio| := by
      apply integral_mono hintegrable.norm
        (hcutoff.norm.const_mul (kernelBound / (frequency * threshold ^ 2)))
      intro ratio
      change |parameterCutoff ratio * frequency *
        kernel (frequency * addressPairDifference first second third fourth ratio)| ≤
          (kernelBound / (frequency * threshold ^ 2)) * |parameterCutoff ratio|
      by_cases hzero : parameterCutoff ratio = 0
      · simp only [hzero, zero_mul, abs_zero, mul_zero, le_refl]
      · rw [abs_mul, abs_mul, abs_of_pos hfrequency]
        calc
          _ = |parameterCutoff ratio| *
              (frequency * |kernel (frequency * addressPairDifference first second third fourth ratio)|) := by ring
          _ ≤ |parameterCutoff ratio| * (kernelBound / (frequency * threshold ^ 2)) :=
            mul_le_mul_of_nonneg_left (hscaled ratio hzero) (abs_nonneg _)
          _ = _ := by ring
    _ = _ := integral_const_mul _ _

/-- The concrete off-band scale from equation (small-value-band). This is
the manuscript's O((depth+1)^2 / (frequency * lower^(2*depth))) contribution. -/
theorem addressPairAnnulus_off_firstDifference_band_bound
    (parameterCutoff kernel : ℝ → ℝ) {frequency kernelBound epsilon lower : ℝ}
    (first second third fourth : ℕ → Bool) (depth : ℕ)
    (hfrequency : 0 < frequency) (hepsilon : 0 < epsilon) (hlower : 0 < lower)
    (hschwartz : ∀ point, |point| ^ 2 * |kernel point| ≤ kernelBound)
    (hsupport : ∀ ratio, parameterCutoff ratio ≠ 0 →
      epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) ≤
        |addressPairDifference first second third fourth ratio|)
    (hcutoff : Integrable parameterCutoff volume)
    (hintegrable : Integrable (fun ratio => parameterCutoff ratio * frequency *
      kernel (frequency * addressPairDifference first second third fourth ratio)) volume) :
    |addressPairAnnulus parameterCutoff kernel frequency first second third fourth| ≤
      (kernelBound * ((depth + 1 : ℕ) : ℝ) ^ 2 /
        (frequency * epsilon ^ 2 * lower ^ (2 * depth))) * ∫ ratio, |parameterCutoff ratio| := by
  have hbound := addressPairAnnulus_off_band_bound parameterCutoff kernel first second third fourth
    hfrequency (by positivity : 0 < epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ))
    hschwartz hsupport hcutoff hintegrable
  have hdepthpos : 0 < ((depth + 1 : ℕ) : ℝ) := by positivity
  convert hbound using 1
  congr 1
  rw [show lower ^ (2 * depth) = (lower ^ depth) ^ 2 by rw [Nat.mul_comm, pow_mul]]
  field_simp [ne_of_gt hfrequency, ne_of_gt hepsilon, ne_of_gt hlower, ne_of_gt hdepthpos]
  <;> ring

end LambdaCantor.AE
