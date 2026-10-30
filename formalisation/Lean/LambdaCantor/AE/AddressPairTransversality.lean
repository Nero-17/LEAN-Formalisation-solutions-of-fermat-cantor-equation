import LambdaCantor.AE.AddressPairKernel
import LambdaCantor.AE.DigitResidual

open Set Filter
open scoped Topology

namespace LambdaCantor.AE

/-- Exact derivative of the actual four-address residual, obtained from
its normalized series on a neighbourhood inside the convergence interval. -/
theorem hasDerivAt_addressPairDifference
    (first second third fourth : ℕ → Bool) (depth : ℕ)
    (hprefix : ∀ index < depth, pairDigitDifference first second third fourth index = 0)
    (hnonzero : pairDigitDifference first second third fourth depth ≠ 0)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    HasDerivAt (addressPairDifference first second third fourth)
      (pairDigitDifference first second third fourth depth *
        (deriv (firstDifferencePrefactor depth) ratio *
          normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio +
          firstDifferencePrefactor depth ratio *
            deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth)) ratio)) ratio := by
  have hseries := hasDerivAt_normalizedDifference
    (normalizedPairCoefficients first second third fourth depth)
    (normalizedPairCoefficients_bound first second third fourth depth hnonzero) hpos hlt
  rw [← hseries.deriv] at hseries
  apply (hasDerivAt_digitResidual depth (pairDigitDifference first second third fourth depth)
    hseries).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Ioo (0 : ℝ) 1 from ⟨hpos, hlt⟩)]
    with nearby hnearby
  simpa only [firstDifferencePrefactor, mul_assoc] using
    addressPairDifference_eq_normalized first second third fourth depth hprefix hnonzero
      hnearby.1 hnearby.2

/-- The uniform small-band derivative bound instantiated for actual address
pairs. Orienting the pair so its leading convolution-digit difference is
positive makes Q decreasing; the constants do not depend on the addresses
or on their first-difference depth. -/
theorem addressPairDifference_uniform_transversality
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2) :
    ∃ epsilon constant : ℝ, 0 < epsilon ∧ 0 < constant ∧
      ∀ (first second third fourth : ℕ → Bool) (depth : ℕ),
        (∀ index < depth, pairDigitDifference first second third fourth index = 0) →
        0 < pairDigitDifference first second third fourth depth →
        ∀ ratio ∈ Icc lower upper,
          |addressPairDifference first second third fourth ratio| <
            epsilon * lower ^ depth / ((depth + 1 : ℕ) : ℝ) →
          deriv (addressPairDifference first second third fourth) ratio ≤ -constant * lower ^ depth := by
  obtain ⟨normalizedBand, margin, hnormalizedBand, hmargin, htransverse⟩ :=
    normalizedDifference_uniform_transversality hlower horder hupper
  have hgap : 0 < 1 - upper := by linarith
  have hnegative_margin : -(margin * (1 - upper) / 2) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (mul_nonneg hmargin.le hgap.le) (by norm_num))
  refine ⟨min (normalizedBand * (1 - upper) / 2)
      (margin * lower * (1 - upper) ^ 2 / 2), margin * (1 - upper) / 2,
    lt_min (by positivity) (by positivity), by positivity, ?_⟩
  intro first second third fourth depth hprefix hdigit ratio hratio hsmall
  have hnonzero := ne_of_gt hdigit
  have hdepth : 0 < ((depth + 1 : ℕ) : ℝ) := by positivity
  have hdepthone : (1 : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le depth)
  have hsmallNormalized := normalized_value_small_of_digitResidual_small depth
    (one_le_abs_pairDigitDifference first second third fourth depth hnonzero)
    hlower hratio (by linarith : upper < 1)
    (show |pairDigitDifference first second third fourth depth * firstDifferencePrefactor depth ratio *
      normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio| <
      min (normalizedBand * (1 - upper) / 2) (margin * lower * (1 - upper) ^ 2 / 2) *
        lower ^ depth / ((depth + 1 : ℕ) : ℝ) by
      simpa only [firstDifferencePrefactor, mul_assoc,
        addressPairDifference_eq_normalized first second third fourth depth hprefix hnonzero
          (hlower.trans_le hratio.1) (by linarith [hratio.2] : ratio < 1)] using hsmall)
  have hnormalizedSmall :
      |normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio| < normalizedBand := by
    apply hsmallNormalized.trans_le
    apply (div_le_iff₀ (mul_pos hgap hdepth)).mpr
    have hmin := min_le_left (normalizedBand * (1 - upper) / 2)
      (margin * lower * (1 - upper) ^ 2 / 2)
    have hmul := mul_le_mul_of_nonneg_left hdepthone (mul_nonneg hnormalizedBand.le hgap.le)
    nlinarith
  have hdominanceSmall :
      |normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio| ≤
        margin * lower * (1 - upper) / (2 * ((depth + 1 : ℕ) : ℝ)) := by
    apply hsmallNormalized.le.trans
    have hdivide : min (normalizedBand * (1 - upper) / 2)
        (margin * lower * (1 - upper) ^ 2 / 2) / (1 - upper) ≤ margin * lower * (1 - upper) / 2 := by
      apply (div_le_iff₀ hgap).mpr
      have hmin := min_le_right (normalizedBand * (1 - upper) / 2)
        (margin * lower * (1 - upper) ^ 2 / 2)
      nlinarith
    have hquotient := div_le_div_of_nonneg_right hdivide hdepth.le
    simpa only [div_div, mul_comm (2 : ℝ) ((depth + 1 : ℕ) : ℝ)] using hquotient
  have hnormalizedDerivative := htransverse
    (normalizedPairCoefficients first second third fourth depth)
    (normalizedPairCoefficients_bound first second third fourth depth hnonzero)
    ratio hratio hnormalizedSmall
  have hdominance := digitResidual_derivative_negative depth hlower hratio
    (by linarith : upper < 1) hmargin hnormalizedDerivative.le hdominanceSmall
  have hinnerNonpos : deriv (firstDifferencePrefactor depth) ratio *
      normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio +
      firstDifferencePrefactor depth ratio *
        deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth)) ratio ≤ 0 :=
    hdominance.trans (mul_nonpos_of_nonpos_of_nonneg hnegative_margin
      (pow_nonneg (hlower.trans_le hratio.1).le depth))
  have hdigitOne : 1 ≤ pairDigitDifference first second third fourth depth := by
    simpa only [abs_of_pos hdigit] using
      one_le_abs_pairDigitDifference first second third fourth depth hnonzero
  rw [(hasDerivAt_addressPairDifference first second third fourth depth hprefix hnonzero
    (hlower.trans_le hratio.1) (by linarith [hratio.2] : ratio < 1)).deriv]
  calc
    _ ≤ deriv (firstDifferencePrefactor depth) ratio *
        normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio +
        firstDifferencePrefactor depth ratio *
          deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth)) ratio := by
      simpa only [one_mul] using mul_le_mul_of_nonpos_right hdigitOne hinnerNonpos
    _ ≤ -(margin * (1 - upper) / 2) * ratio ^ depth := hdominance
    _ ≤ _ := mul_le_mul_of_nonpos_left
      (pow_le_pow_left₀ hlower.le hratio.1 depth) hnegative_margin

end LambdaCantor.AE
