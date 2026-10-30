import LambdaCantor.AE.CenteredResonance
import LambdaCantor.AE.CenteredNormalizedBounds

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

theorem centered_actual_remainder_bound {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hless : ratio < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    (hsmall : ratio ^ verticalDepth ≤ 1 / 2) :
    |ratio ^ (-exponent * (horizontalDepth : ℝ)) *
      centeredTaylorRemainder exponent
        (centeredAddressDisplacement verticalDepth tailDepth digits ratio)| ≤
      (exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))) *
        (ratio ^ (-exponent * (horizontalDepth : ℝ)) * (ratio ^ verticalDepth) ^ 2) := by
  have hdisplacement := centeredAddressDisplacement_bounds verticalDepth tailDepth digits hpositive hless
  have hquadratic := centeredTaylorRemainder_quadratic_bound hexponent
    (show centeredAddressDisplacement verticalDepth tailDepth digits ratio ∈ Set.Icc (0 : ℝ) (1 / 2) from
      ⟨hdisplacement.1, hdisplacement.2.trans hsmall⟩)
  have hsquare := pow_le_pow_left₀ hdisplacement.1 hdisplacement.2 2
  have hconstant : 0 ≤ exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) := by
    have : 0 ≤ exponent := by linarith
    have : 0 ≤ exponent - 1 := by linarith
    positivity
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hpositive.le _)]
  calc
    _ ≤ ratio ^ (-exponent * (horizontalDepth : ℝ)) *
        ((exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))) *
          (ratio ^ verticalDepth) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (hquadratic.trans (mul_le_mul_of_nonneg_left hsquare hconstant))
        (Real.rpow_nonneg hpositive.le _)
    _ = _ := by ring

/-- An actual centered remainder tends to zero uniformly in arbitrary
choices of addresses and parameters once the normalized envelope decays. -/
theorem centered_actual_remainder_tendsto_zero
    {exponent lower upper : ℝ} (hexponent : 1 < exponent)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hless : upper < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (hdepth : ∀ index, index ≤ verticalDepth index)
    (htwo : ∀ index, 2 ≤ verticalDepth index)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper)
    (digits : ℕ → ℕ → Bool)
    (henvelope : Tendsto (fun index => (verticalDepth index : ℝ) ^ 2 *
      ((ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
        ((ratios index) ^ verticalDepth index) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun index => (ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
      centeredTaylorRemainder exponent
        (centeredAddressDisplacement (verticalDepth index) index (digits index) (ratios index)))
      atTop (𝓝 0) := by
  have hconstant : 0 ≤ exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) := by
    have : 0 ≤ exponent := by linarith
    have : 0 ≤ exponent - 1 := by linarith
    positivity
  have hsmall : ∀ᶠ index : ℕ in atTop, upper ^ index < (1 / 2 : ℝ) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hlower.le.trans hinterval) hless).eventually
      (gt_mem_nhds (by norm_num))
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  apply squeeze_zero'
    (g := fun index : ℕ =>
      (exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))) *
        ((verticalDepth index : ℝ) ^ 2 *
          ((ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
            ((ratios index) ^ verticalDepth index) ^ 2)))
    (Eventually.of_forall (fun _ => abs_nonneg _))
  · filter_upwards [hsmall] with index hsmall
    have hpositive := hlower.trans_le (hratios index).1
    have hpower : (ratios index) ^ verticalDepth index ≤ 1 / 2 :=
      ((pow_le_pow_left₀ hpositive.le (hratios index).2 _).trans
        (pow_le_pow_of_le_one (hlower.le.trans hinterval) hless.le (hdepth index))).trans hsmall.le
    have hbound := centered_actual_remainder_bound hexponent hpositive
      ((hratios index).2.trans_lt hless) (horizontalDepth index) (verticalDepth index)
      index (digits index) hpower
    have hdepthReal : (2 : ℝ) ≤ verticalDepth index := by exact_mod_cast htwo index
    have hsquare : (1 : ℝ) ≤ (verticalDepth index : ℝ) ^ 2 := by nlinarith
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left
        (mul_nonneg (Real.rpow_nonneg hpositive.le _) (sq_nonneg _)) hsquare) hconstant)
  · simpa only [mul_zero] using henvelope.const_mul
      (exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)))

end LambdaCantor.AE
