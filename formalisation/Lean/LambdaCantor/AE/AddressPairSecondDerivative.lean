import LambdaCantor.AE.AddressPairTransversality
import LambdaCantor.AE.UniformSeriesBounds
import LambdaCantor.AE.ResidualRegularity
import LambdaCantor.AE.DigitResidualBounds

open Set Filter
open scoped Topology

namespace LambdaCantor.AE

theorem hasDerivAt_deriv_addressPairDifference
    (first second third fourth : ℕ → Bool) (depth : ℕ)
    (hprefix : ∀ index < depth, pairDigitDifference first second third fourth index = 0)
    (hnonzero : pairDigitDifference first second third fourth depth ≠ 0)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    HasDerivAt (deriv (addressPairDifference first second third fourth))
      (pairDigitDifference first second third fourth depth *
        (deriv (deriv (firstDifferencePrefactor depth)) ratio *
          normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio +
          2 * deriv (firstDifferencePrefactor depth) ratio *
            deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth)) ratio +
          firstDifferencePrefactor depth ratio *
            deriv (deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth))) ratio)) ratio := by
  have hcoefficients := normalizedPairCoefficients_bound first second third fourth depth hnonzero
  have hseriesSecond := hasDerivAt_deriv_normalizedDifference
    (normalizedPairCoefficients first second third fourth depth) hcoefficients hpos hlt
  rw [← hseriesSecond.deriv] at hseriesSecond
  have hlocalFirst : ∀ᶠ nearby in 𝓝 ratio,
      HasDerivAt (normalizedDifference (normalizedPairCoefficients first second third fourth depth))
        (deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth)) nearby) nearby := by
    filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Ioo (0 : ℝ) 1 from ⟨hpos, hlt⟩)] with nearby hnearby
    exact (hasDerivAt_normalizedDifference
      (normalizedPairCoefficients first second third fourth depth) hcoefficients hnearby.1 hnearby.2).differentiableAt.hasDerivAt
  have hequality : addressPairDifference first second third fourth =ᶠ[𝓝 ratio]
      (fun nearby => pairDigitDifference first second third fourth depth *
        firstDifferencePrefactor depth nearby *
        normalizedDifference (normalizedPairCoefficients first second third fourth depth) nearby) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Ioo (0 : ℝ) 1 from ⟨hpos, hlt⟩)] with nearby hnearby
    simpa only [firstDifferencePrefactor, mul_assoc] using
      addressPairDifference_eq_normalized first second third fourth depth hprefix hnonzero hnearby.1 hnearby.2
  exact (hasDerivAt_deriv_digitResidual_local depth (pairDigitDifference first second third fourth depth)
    hlocalFirst hseriesSecond).congr_of_eventuallyEq hequality.deriv

/-- The uniform second-derivative estimate in (small-value-band), proved
for the actual residual on the whole compact parameter interval. -/
theorem addressPairDifference_uniform_secondDerivative_bound
    {lower upper : ℝ} (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (first second third fourth : ℕ → Bool) (depth : ℕ),
        (∀ index < depth, pairDigitDifference first second third fourth index = 0) →
        pairDigitDifference first second third fourth depth ≠ 0 →
        ∀ ratio ∈ Icc lower upper,
          |deriv (deriv (addressPairDifference first second third fourth)) ratio| ≤
            constant * ((depth + 1 : ℕ) : ℝ) ^ 2 * upper ^ depth := by
  obtain ⟨seriesBound, hseriesBound, hseries⟩ :=
    normalizedDifference_uniform_C2_bounds (hlower.trans_le horder) hupper
  refine ⟨2 * ((2 / lower + 1 / lower ^ 2) + 2 / lower + 1) * seriesBound,
    by positivity, ?_⟩
  intro first second third fourth depth hprefix hnonzero ratio hratio
  have hratiopos := hlower.trans_le hratio.1
  have hratioone := hratio.2.trans_lt hupper
  have hcoefficients := normalizedPairCoefficients_bound first second third fourth depth hnonzero
  obtain ⟨hvalue, hfirst, hsecond⟩ := hseries
    (normalizedPairCoefficients first second third fourth depth) hcoefficients ratio ⟨hratiopos, hratio.2⟩
  have hprefactorFirst := firstDifferencePrefactor_derivative_bound depth hlower hratio.1 hratioone
  have hprefactorSecond := firstDifferencePrefactor_secondDerivative_bound depth hlower hratio.1 hratioone
  have hprefactor : |firstDifferencePrefactor depth ratio| ≤ ratio ^ depth := by
    rw [abs_of_pos (firstDifferencePrefactor_pos depth hratiopos hratioone)]
    unfold firstDifferencePrefactor
    nlinarith [pow_nonneg hratiopos.le depth,
      mul_nonneg hratiopos.le (pow_nonneg hratiopos.le depth)]
  have hdepthone : (1 : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le depth)
  have hdepthsquare : ((depth + 1 : ℕ) : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hdepthsquareone : (1 : ℝ) ≤ ((depth + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have htermFirst := mul_le_mul hprefactorSecond hvalue (abs_nonneg _)
    (by positivity : 0 ≤ (2 / lower + 1 / lower ^ 2) * ((depth + 1 : ℕ) : ℝ) ^ 2 * ratio ^ depth)
  have htermMiddle := mul_le_mul hprefactorFirst hfirst (abs_nonneg _)
    (by positivity : 0 ≤ ((depth + 1 : ℕ) : ℝ) / lower * ratio ^ depth)
  have htermLast := mul_le_mul hprefactor hsecond (abs_nonneg _) (pow_nonneg hratiopos.le depth)
  have hmiddleGrowth := mul_le_mul_of_nonneg_right hdepthsquare
    (show 0 ≤ (2 / lower) * seriesBound * ratio ^ depth by positivity)
  have hlastGrowth := mul_le_mul_of_nonneg_right hdepthsquareone
    (show 0 ≤ seriesBound * ratio ^ depth by positivity)
  have hinner :
      |deriv (deriv (firstDifferencePrefactor depth)) ratio *
          normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio +
        2 * deriv (firstDifferencePrefactor depth) ratio *
          deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth)) ratio +
        firstDifferencePrefactor depth ratio *
          deriv (deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth))) ratio| ≤
      (((2 / lower + 1 / lower ^ 2) + 2 / lower + 1) * seriesBound) *
        ((depth + 1 : ℕ) : ℝ) ^ 2 * ratio ^ depth := by
    calc
      _ ≤ |deriv (deriv (firstDifferencePrefactor depth)) ratio *
            normalizedDifference (normalizedPairCoefficients first second third fourth depth) ratio| +
          |2 * deriv (firstDifferencePrefactor depth) ratio *
            deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth)) ratio| +
          |firstDifferencePrefactor depth ratio *
            deriv (deriv (normalizedDifference (normalizedPairCoefficients first second third fourth depth))) ratio| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ _ := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc
          _ ≤ (2 / lower + 1 / lower ^ 2) * ((depth + 1 : ℕ) : ℝ) ^ 2 *
                ratio ^ depth * seriesBound +
              2 * (((depth + 1 : ℕ) : ℝ) / lower * ratio ^ depth * seriesBound) +
              ratio ^ depth * seriesBound := by
            apply add_le_add _ htermLast
            apply add_le_add htermFirst
            simpa only [mul_assoc] using
              mul_le_mul_of_nonneg_left htermMiddle (show (0 : ℝ) ≤ 2 by norm_num)
          _ = (2 / lower + 1 / lower ^ 2) * ((depth + 1 : ℕ) : ℝ) ^ 2 *
                ratio ^ depth * seriesBound +
              ((depth + 1 : ℕ) : ℝ) * ((2 / lower) * seriesBound * ratio ^ depth) +
              1 * (seriesBound * ratio ^ depth) := by ring
          _ ≤ (2 / lower + 1 / lower ^ 2) * ((depth + 1 : ℕ) : ℝ) ^ 2 *
                ratio ^ depth * seriesBound +
              ((depth + 1 : ℕ) : ℝ) ^ 2 * ((2 / lower) * seriesBound * ratio ^ depth) +
              ((depth + 1 : ℕ) : ℝ) ^ 2 * (seriesBound * ratio ^ depth) :=
            add_le_add (add_le_add (le_refl _) hmiddleGrowth) hlastGrowth
          _ = _ := by ring
  rw [(hasDerivAt_deriv_addressPairDifference first second third fourth depth hprefix hnonzero
    hratiopos hratioone).deriv, abs_mul]
  calc
    _ ≤ 2 * ((((2 / lower + 1 / lower ^ 2) + 2 / lower + 1) * seriesBound) *
        ((depth + 1 : ℕ) : ℝ) ^ 2 * ratio ^ depth) :=
      mul_le_mul (abs_pairDigitDifference_le_two first second third fourth depth) hinner
        (abs_nonneg _) (by norm_num)
    _ ≤ _ := by
      have hpower := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hratiopos.le hratio.2 depth)
        (show 0 ≤ 2 * ((2 / lower + 1 / lower ^ 2) + 2 / lower + 1) * seriesBound *
          ((depth + 1 : ℕ) : ℝ) ^ 2 by positivity)
      simpa only [mul_assoc] using hpower

end LambdaCantor.AE
