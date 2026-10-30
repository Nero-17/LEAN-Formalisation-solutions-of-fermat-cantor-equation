import LambdaCantor.Last.IrrationalRescaling
import LambdaCantor.AE.CenteredPowerBounds

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

/-- The normalization cancels one of the two small displacement factors.
Keeping this identity pointwise avoids an exponentially bad lower-endpoint
estimate for the normalization itself. -/
theorem centered_normalization_identity {ratio exponent : ℝ} (hpositive : 0 < ratio)
    (horizontalDepth verticalDepth : ℕ) :
    ratio ^ (-exponent * (horizontalDepth : ℝ)) * (ratio ^ verticalDepth) ^ 2 =
      ratio ^ verticalDepth * ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) := by
  rw [← Real.rpow_natCast ratio verticalDepth]
  rw [← Real.rpow_mul_natCast hpositive.le, ← Real.rpow_add hpositive,
    ← Real.rpow_add hpositive]
  congr 1
  ring

/-- Differentiating the normalization costs a fixed inverse power of the
lower endpoint while retaining the pointwise normalization factor. -/
theorem centered_shifted_normalization_bound {lower ratio scaleExponent : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (offset : ℕ) :
    ratio ^ (scaleExponent - (offset : ℝ)) ≤ ratio ^ scaleExponent / lower ^ offset := by
  rw [Real.rpow_sub (hlower.trans_le hratio), Real.rpow_natCast]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg (hlower.le.trans hratio) _)
    (pow_pos hlower _) (pow_le_pow_left₀ hlower.le hratio offset)

/-- A bounded resonance exponent is uniformly harmless on a compact
parameter interval. Only a lower bound for the exponent is needed. -/
theorem centered_resonance_factor_bound {lower ratio discrepancy bound : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (hless : ratio ≤ 1)
    (hbound : 0 ≤ bound) (hdiscrepancy : -bound ≤ discrepancy) :
    ratio ^ discrepancy ≤ lower ^ (-bound) :=
  (Real.rpow_le_rpow_of_exponent_ge (hlower.trans_le hratio) hless hdiscrepancy).trans
    (Real.rpow_le_rpow_of_nonpos hlower hratio (neg_nonpos.mpr hbound))

theorem centered_normalization_uniform_bound {lower ratio upper exponent bound : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (hupper : ratio ≤ upper)
    (hless : upper < 1) (hbound : 0 ≤ bound)
    (horizontalDepth verticalDepth : ℕ)
    (hdiscrepancy : -bound ≤ (verticalDepth : ℝ) - exponent * horizontalDepth) :
    ratio ^ (-exponent * (horizontalDepth : ℝ)) * (ratio ^ verticalDepth) ^ 2 ≤
      upper ^ verticalDepth * lower ^ (-bound) := by
  rw [centered_normalization_identity (hlower.trans_le hratio)]
  exact mul_le_mul
    (pow_le_pow_left₀ (hlower.le.trans hratio) hupper verticalDepth)
    (centered_resonance_factor_bound hlower hratio (hupper.trans hless.le) hbound hdiscrepancy)
    (Real.rpow_nonneg (hlower.le.trans hratio) _) (pow_nonneg (hlower.le.trans (hratio.trans hupper)) _)

/-- Irrationality allows arbitrary simultaneous depth and exponential-tail
requirements; this uses density after a cutoff, not a Diophantine rate. -/
theorem centered_irrational_depth_choice {exponent upper epsilon tolerance : ℝ}
    (hirrational : Irrational exponent) (hexponent : 0 < exponent)
    (hupper : 0 ≤ upper) (hless : upper < 1)
    (hepsilon : 0 < epsilon) (htolerance : 0 < tolerance)
    (target : ℝ) (minimumDepth : ℕ) :
    ∃ horizontalDepth verticalDepth : ℕ,
      minimumDepth ≤ horizontalDepth ∧ minimumDepth ≤ verticalDepth ∧
      |(verticalDepth : ℝ) - exponent * horizontalDepth - target| < epsilon ∧
      (verticalDepth : ℝ) ^ 2 * upper ^ verticalDepth < tolerance := by
  have hnorm : ‖upper‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hupper]
  have hdecay := (summable_pow_mul_geometric_of_norm_lt_one 2 hnorm).tendsto_atTop_zero
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp (hdecay.eventually (gt_mem_nhds htolerance))
  obtain ⟨horizontalDepth, verticalDepth, hhorizontal, hvertical, happroximation⟩ :=
    Last.irrational_natural_difference_approximation hirrational hexponent target hepsilon
      (max minimumDepth cutoff)
  exact ⟨horizontalDepth, verticalDepth, (le_max_left _ _).trans hhorizontal,
    (le_max_left _ _).trans hvertical, happroximation,
    hcutoff verticalDepth ((le_max_right _ _).trans hvertical)⟩

/-- Exact depth hypotheses used by the centered cylinders in the paper. -/
theorem centered_paper_depth_choice {exponent center upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hcenter : 0 < center) (hupper : 0 ≤ upper) (hless : upper < 1)
    (tailDepth : ℕ) :
    ∃ horizontalDepth verticalDepth : ℕ,
      tailDepth ≤ horizontalDepth ∧ tailDepth ≤ verticalDepth ∧ 2 ≤ verticalDepth ∧
      |(verticalDepth : ℝ) - exponent * horizontalDepth + Real.log exponent / Real.log center| <
        (center ^ tailDepth) ^ 2 ∧
      (verticalDepth : ℝ) ^ 2 * upper ^ verticalDepth < (center ^ tailDepth) ^ 3 := by
  obtain ⟨horizontalDepth, verticalDepth, hhorizontal, hvertical, happroximation, hdecay⟩ :=
    centered_irrational_depth_choice hirrational (by linarith) hupper hless
      (show 0 < (center ^ tailDepth) ^ 2 by positivity)
      (show 0 < (center ^ tailDepth) ^ 3 by positivity)
      (-Real.log exponent / Real.log center) (max tailDepth 2)
  refine ⟨horizontalDepth, verticalDepth, (le_max_left _ _).trans hhorizontal,
    (le_max_left _ _).trans hvertical, (le_max_right _ _).trans hvertical, ?_, hdecay⟩
  simpa only [neg_div, sub_neg_eq_add] using happroximation

theorem centered_discrepancy_lower_bound {discrepancy target epsilon : ℝ}
    (happroximation : |discrepancy - target| ≤ epsilon) (hepsilon : epsilon ≤ 1) :
    -(|target| + 1) ≤ discrepancy := by
  have hlower := (abs_le.mp happroximation).1
  have htarget := neg_abs_le target
  linarith

/-- The polynomial loss of two parameter derivatives still decays after
normalization, with a constant independent of either cylinder depth. -/
theorem centered_normalized_quadratic_decay
    {lower ratio upper exponent target epsilon tolerance : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (hupper : ratio ≤ upper)
    (hless : upper < 1) (horizontalDepth verticalDepth : ℕ)
    (happroximation : |(verticalDepth : ℝ) - exponent * horizontalDepth - target| ≤ epsilon)
    (hepsilon : epsilon ≤ 1)
    (hdecay : (verticalDepth : ℝ) ^ 2 * upper ^ verticalDepth ≤ tolerance) :
    (verticalDepth : ℝ) ^ 2 *
        (ratio ^ (-exponent * (horizontalDepth : ℝ)) * (ratio ^ verticalDepth) ^ 2) ≤
      lower ^ (-(|target| + 1)) * tolerance := by
  have hnormalized := centered_normalization_uniform_bound hlower hratio hupper hless
    (show 0 ≤ |target| + 1 by positivity) horizontalDepth verticalDepth
    (centered_discrepancy_lower_bound happroximation hepsilon)
  calc
    _ ≤ (verticalDepth : ℝ) ^ 2 *
        (upper ^ verticalDepth * lower ^ (-(|target| + 1))) :=
      mul_le_mul_of_nonneg_left hnormalized (sq_nonneg _)
    _ = lower ^ (-(|target| + 1)) * ((verticalDepth : ℝ) ^ 2 * upper ^ verticalDepth) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg hlower.le _)

theorem centered_normalization_exponent_bound
    {exponent target epsilon : ℝ} (hexponent : 0 ≤ exponent)
    (horizontalDepth verticalDepth : ℕ) (hdepth : 1 ≤ verticalDepth)
    (happroximation : |(verticalDepth : ℝ) - exponent * horizontalDepth - target| ≤ epsilon)
    (hepsilon : epsilon ≤ 1) :
    |-exponent * (horizontalDepth : ℝ)| ≤ (|target| + 2) * verticalDepth := by
  have hdiscrepancy := centered_discrepancy_lower_bound happroximation hepsilon
  have hdepthReal : (1 : ℝ) ≤ verticalDepth := by exact_mod_cast hdepth
  have hproduct := mul_nonneg (abs_nonneg target) (sub_nonneg.mpr hdepthReal)
  rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hexponent (Nat.cast_nonneg _))]
  nlinarith

/-- The actual irrational choices give a uniform, depth-independent bound
for the normalized quadratic error across the entire parameter interval. -/
theorem centered_paper_normalized_depth_choice {exponent center lower upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hcenter : 0 < center) (hcenterLess : center < 1)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1)
    (tailDepth : ℕ) :
    ∃ horizontalDepth verticalDepth : ℕ,
      tailDepth ≤ horizontalDepth ∧ tailDepth ≤ verticalDepth ∧ 2 ≤ verticalDepth ∧
      |(verticalDepth : ℝ) - exponent * horizontalDepth + Real.log exponent / Real.log center| <
        (center ^ tailDepth) ^ 2 ∧
      (verticalDepth : ℝ) ^ 2 * upper ^ verticalDepth < (center ^ tailDepth) ^ 3 ∧
      ∀ ratio ∈ Set.Icc lower upper,
        (verticalDepth : ℝ) ^ 2 *
          (ratio ^ (-exponent * (horizontalDepth : ℝ)) * (ratio ^ verticalDepth) ^ 2) ≤
        lower ^ (-(|Real.log exponent / Real.log center| + 1)) * (center ^ tailDepth) ^ 3 := by
  obtain ⟨horizontalDepth, verticalDepth, hhorizontal, hvertical, htwo, happroximation, hdecay⟩ :=
    centered_paper_depth_choice hirrational hexponent hcenter (hlower.le.trans hinterval) hless tailDepth
  refine ⟨horizontalDepth, verticalDepth, hhorizontal, hvertical, htwo, happroximation, hdecay, ?_⟩
  intro ratio hratio
  have hscale : (center ^ tailDepth) ^ 2 ≤ 1 :=
    pow_le_one₀ (pow_nonneg hcenter.le _) (pow_le_one₀ hcenter.le hcenterLess.le) 
  have hphase : |(verticalDepth : ℝ) - exponent * horizontalDepth -
      (-Real.log exponent / Real.log center)| ≤ (center ^ tailDepth) ^ 2 := by
    simpa only [neg_div, sub_neg_eq_add] using happroximation.le
  simpa only [neg_div, abs_neg] using centered_normalized_quadratic_decay
    hlower hratio.1 hratio.2 hless horizontalDepth verticalDepth hphase hscale hdecay.le

/-- One choice for every tail depth has a normalized quadratic envelope
converging to zero even along arbitrary parameter sequences in the band. -/
theorem centered_normalized_depth_sequences {exponent center lower upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hcenter : 0 < center) (hcenterLess : center < 1)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1) :
    ∃ horizontalDepth verticalDepth : ℕ → ℕ,
      (∀ tailDepth, tailDepth ≤ horizontalDepth tailDepth ∧
        tailDepth ≤ verticalDepth tailDepth ∧ 2 ≤ verticalDepth tailDepth) ∧
      (∀ tailDepth,
        |(verticalDepth tailDepth : ℝ) - exponent * horizontalDepth tailDepth +
            Real.log exponent / Real.log center| < (center ^ tailDepth) ^ 2 ∧
        (verticalDepth tailDepth : ℝ) ^ 2 * upper ^ verticalDepth tailDepth <
          (center ^ tailDepth) ^ 3) ∧
      ∀ ratios : ℕ → ℝ, (∀ index, ratios index ∈ Set.Icc lower upper) →
        Tendsto (fun index => (verticalDepth index : ℝ) ^ 2 *
          ((ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
            ((ratios index) ^ verticalDepth index) ^ 2)) atTop (𝓝 0) := by
  have hchoices := fun tailDepth => centered_paper_normalized_depth_choice
    hirrational hexponent hcenter hcenterLess hlower hinterval hless tailDepth
  choose horizontalDepth verticalDepth hhorizontal hvertical htwo hphase hdecay henvelope using hchoices
  refine ⟨horizontalDepth, verticalDepth, fun index =>
    ⟨hhorizontal index, hvertical index, htwo index⟩,
    fun index => ⟨hphase index, hdecay index⟩, ?_⟩
  intro ratios hratios
  apply squeeze_zero
  · intro index
    exact mul_nonneg (sq_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (hlower.le.trans (hratios index).1) _) (sq_nonneg _))
  · intro index
    exact henvelope index (ratios index) (hratios index)
  · have hscale := (tendsto_pow_atTop_nhds_zero_of_lt_one hcenter.le hcenterLess).pow 3
    simpa only [zero_pow (by omega : (3 : ℕ) ≠ 0), mul_zero] using
      hscale.const_mul (lower ^ (-(|Real.log exponent / Real.log center| + 1)))

end LambdaCantor.AE
