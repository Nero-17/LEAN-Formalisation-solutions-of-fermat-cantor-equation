import LambdaCantor.AE.CenteredRemainderDerivatives

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

/-- The actual second derivative tends to zero along arbitrary addresses
and parameter choices. All dependence on the depth has been absorbed in
the normalized envelope. -/
theorem centeredRemainderSecond_tendsto_zero
    {exponent lower upper target firstBound secondBound : ℝ}
    (hexponent : 1 < exponent) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (hless : upper < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (hdepth : ∀ index, index ≤ verticalDepth index)
    (htwo : ∀ index, 2 ≤ verticalDepth index)
    (hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index - target| ≤ 1)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper)
    (digits : ℕ → ℕ → Bool)
    (hfirst : ∀ index, |deriv (fun parameter => address parameter (digits index)) (ratios index)| ≤ firstBound)
    (hsecond : ∀ index, |deriv (deriv (fun parameter => address parameter (digits index))) (ratios index)| ≤ secondBound)
    (henvelope : Tendsto (fun index => (verticalDepth index : ℝ) ^ 2 *
      ((ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
        ((ratios index) ^ verticalDepth index) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun index => centeredRemainderSecond exponent (horizontalDepth index)
      (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0) := by
  let taylorBound := exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))
  let velocityBound := 3 / lower + firstBound
  let accelerationBound := 5 / lower ^ 2 + 4 * firstBound / lower + secondBound
  let exponentBound := |target| + 2
  let derivativeBound := exponentBound * (exponentBound + 1) / lower ^ 2 * taylorBound +
    2 * exponentBound / lower * taylorBound * velocityBound +
      taylorBound * velocityBound ^ 2 + taylorBound * accelerationBound
  have hsmall : ∀ᶠ index : ℕ in atTop, upper ^ index < (1 / 2 : ℝ) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hlower.le.trans hinterval) hless).eventually
      (gt_mem_nhds (by norm_num))
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
  · filter_upwards [hsmall] with index hsmall
    have hpositive := hlower.trans_le (hratios index).1
    have hpower : (ratios index) ^ verticalDepth index ≤ 1 / 2 :=
      ((pow_le_pow_left₀ hpositive.le (hratios index).2 _).trans
        (pow_le_pow_of_le_one (hlower.le.trans hinterval) hless.le (hdepth index))).trans hsmall.le
    have hbound := centeredRemainderSecond_bound hexponent hlower (hratios index).1
      ((hratios index).2.trans_lt hless) (horizontalDepth index) (verticalDepth index) index
      (htwo index) (hdepth index) (digits index) hpower (hphase index) le_rfl
      (hfirst index) (hsecond index) (le_refl taylorBound) (le_refl velocityBound)
      (le_refl accelerationBound) (le_refl exponentBound)
    change |centeredRemainderSecond exponent (horizontalDepth index) (verticalDepth index)
      index (digits index) (ratios index)| ≤ derivativeBound *
        ((verticalDepth index : ℝ) ^ 2 * ((ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
          ((ratios index) ^ verticalDepth index) ^ 2))
    calc
      _ ≤ _ := hbound
      _ = _ := by
        dsimp only [derivativeBound]
        ring
  · simpa only [mul_zero] using henvelope.const_mul derivativeBound

theorem centeredRemainderFirst_tendsto_zero
    {exponent lower upper target firstBound : ℝ}
    (hexponent : 1 < exponent) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (hless : upper < 1)
    (horizontalDepth verticalDepth : ℕ → ℕ)
    (hdepth : ∀ index, index ≤ verticalDepth index)
    (htwo : ∀ index, 2 ≤ verticalDepth index)
    (hphase : ∀ index, |(verticalDepth index : ℝ) - exponent * horizontalDepth index - target| ≤ 1)
    (ratios : ℕ → ℝ) (hratios : ∀ index, ratios index ∈ Set.Icc lower upper)
    (digits : ℕ → ℕ → Bool)
    (hfirst : ∀ index, |deriv (fun parameter => address parameter (digits index)) (ratios index)| ≤ firstBound)
    (henvelope : Tendsto (fun index => (verticalDepth index : ℝ) ^ 2 *
      ((ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
        ((ratios index) ^ verticalDepth index) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun index => centeredRemainderFirst exponent (horizontalDepth index)
      (verticalDepth index) index (digits index) (ratios index)) atTop (𝓝 0) := by
  let taylorBound := exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2))
  let velocityBound := 3 / lower + firstBound
  let exponentBound := |target| + 2
  let derivativeBound := exponentBound / lower * taylorBound + taylorBound * velocityBound
  have hexponentPositive : 0 < exponent := by linarith
  have hexponentMinus : 0 < exponent - 1 := by linarith
  have hfirstNonnegative : 0 ≤ firstBound := (abs_nonneg _).trans (hfirst 0)
  have hderivativeNonnegative : 0 ≤ derivativeBound := by
    dsimp [derivativeBound, exponentBound, taylorBound, velocityBound]
    positivity
  have hsmall : ∀ᶠ index : ℕ in atTop, upper ^ index < (1 / 2 : ℝ) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (hlower.le.trans hinterval) hless).eventually
      (gt_mem_nhds (by norm_num))
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq, sub_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
  · filter_upwards [hsmall] with index hsmall
    have hpositive := hlower.trans_le (hratios index).1
    have hpower : (ratios index) ^ verticalDepth index ≤ 1 / 2 :=
      ((pow_le_pow_left₀ hpositive.le (hratios index).2 _).trans
        (pow_le_pow_of_le_one (hlower.le.trans hinterval) hless.le (hdepth index))).trans hsmall.le
    have hbound := centeredRemainderFirst_bound hexponent hlower (hratios index).1
      ((hratios index).2.trans_lt hless) (horizontalDepth index) (verticalDepth index) index
      (by have := htwo index; omega) (hdepth index) (digits index) hpower (hphase index) le_rfl
      (hfirst index) (le_refl taylorBound) (le_refl velocityBound) (le_refl exponentBound)
    change |centeredRemainderFirst exponent (horizontalDepth index) (verticalDepth index)
      index (digits index) (ratios index)| ≤ derivativeBound *
        ((verticalDepth index : ℝ) ^ 2 * ((ratios index) ^ (-exponent * (horizontalDepth index : ℝ)) *
          ((ratios index) ^ verticalDepth index) ^ 2))
    have hdepthReal : (2 : ℝ) ≤ verticalDepth index := by exact_mod_cast htwo index
    have hsquare : (verticalDepth index : ℝ) ≤ (verticalDepth index : ℝ) ^ 2 := by nlinarith
    apply hbound.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsquare hderivativeNonnegative)
      (mul_nonneg (Real.rpow_nonneg hpositive.le (-exponent * (horizontalDepth index : ℝ)))
        (sq_nonneg ((ratios index) ^ verticalDepth index)))
  · simpa only [mul_zero] using henvelope.const_mul derivativeBound

end LambdaCantor.AE
