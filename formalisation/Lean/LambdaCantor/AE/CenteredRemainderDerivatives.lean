import LambdaCantor.AE.CenteredDerivativeEnvelope
import LambdaCantor.AE.CenteredRemainderDecay

noncomputable section
namespace LambdaCantor.AE

def centeredRemainderFunction (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  ratio ^ (-exponent * (horizontalDepth : ℝ)) * centeredTaylorRemainder exponent
    (centeredAddressDisplacement verticalDepth tailDepth digits ratio)

def centeredRemainderFirst (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  (-exponent * (horizontalDepth : ℝ)) * ratio ^ (-exponent * horizontalDepth - 1) *
      centeredTaylorRemainder exponent (centeredAddressDisplacement verticalDepth tailDepth digits ratio) +
    ratio ^ (-exponent * (horizontalDepth : ℝ)) *
      (centeredTaylorFirst exponent (centeredAddressDisplacement verticalDepth tailDepth digits ratio) *
        centeredDisplacementFirst verticalDepth tailDepth digits ratio)

def centeredRemainderSecond (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  (-exponent * (horizontalDepth : ℝ)) * (-exponent * horizontalDepth - 1) *
      ratio ^ (-exponent * horizontalDepth - 2) *
      centeredTaylorRemainder exponent (centeredAddressDisplacement verticalDepth tailDepth digits ratio) +
    2 * (-exponent * (horizontalDepth : ℝ)) * ratio ^ (-exponent * horizontalDepth - 1) *
      centeredTaylorFirst exponent (centeredAddressDisplacement verticalDepth tailDepth digits ratio) *
      centeredDisplacementFirst verticalDepth tailDepth digits ratio +
    ratio ^ (-exponent * (horizontalDepth : ℝ)) *
      (centeredTaylorSecond exponent (centeredAddressDisplacement verticalDepth tailDepth digits ratio) *
          (centeredDisplacementFirst verticalDepth tailDepth digits ratio) ^ 2 +
        centeredTaylorFirst exponent (centeredAddressDisplacement verticalDepth tailDepth digits ratio) *
          centeredDisplacementSecond verticalDepth tailDepth digits ratio)

theorem centeredRemainderFunction_hasDerivAt (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (hsmall : ratio ^ verticalDepth < 1) :
    HasDerivAt (centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth digits)
      (centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth digits ratio) ratio := by
  have hdisplacement := centeredAddressDisplacement_bounds verticalDepth tailDepth digits hpositive hless
  have hderivative := centeredNormalizedRemainder_hasDerivAt hpositive
    (hdisplacement.2.trans_lt hsmall)
    (centeredDisplacement_first_actual verticalDepth tailDepth digits hpositive hless)
    (exponent := exponent) (scaleExponent := -exponent * (horizontalDepth : ℝ))
  have hfunction := hderivative.congr_of_eventuallyEq
    (f₁ := centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth digits)
    (Filter.Eventually.of_forall (fun _ => rfl))
  simpa only [centeredRemainderFirst, mul_assoc] using hfunction

theorem centeredRemainderFirst_hasDerivAt (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (hsmall : ratio ^ verticalDepth < 1) :
    HasDerivAt (centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth digits)
      (centeredRemainderSecond exponent horizontalDepth verticalDepth tailDepth digits ratio) ratio := by
  have hdisplacement := centeredAddressDisplacement_bounds verticalDepth tailDepth digits hpositive hless
  exact centeredNormalizedRemainder_second hpositive (hdisplacement.2.trans_lt hsmall)
    (centeredDisplacement_first_actual verticalDepth tailDepth digits hpositive hless)
    (centeredDisplacement_second_actual verticalDepth tailDepth digits hpositive hless)

theorem centeredRemainderFirst_bound
    {exponent lower ratio target epsilon firstBound taylorBound velocityBound exponentBound : ℝ}
    (hexponent : 1 < exponent) (hlower : 0 < lower) (hratio : lower ≤ ratio) (hless : ratio < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ) (hdepth : 1 ≤ verticalDepth)
    (htail : tailDepth ≤ verticalDepth) (digits : ℕ → Bool)
    (hsmall : ratio ^ verticalDepth ≤ 1 / 2)
    (hphase : |(verticalDepth : ℝ) - exponent * horizontalDepth - target| ≤ epsilon)
    (hepsilon : epsilon ≤ 1)
    (hfirst : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound)
    (htaylorBound : exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) ≤ taylorBound)
    (hvelocityBound : 3 / lower + firstBound ≤ velocityBound)
    (hexponentBound : |target| + 2 ≤ exponentBound) :
    |centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth digits ratio| ≤
      (exponentBound / lower * taylorBound + taylorBound * velocityBound) *
        (verticalDepth : ℝ) *
        (ratio ^ (-exponent * (horizontalDepth : ℝ)) * (ratio ^ verticalDepth) ^ 2) := by
  have hpositive := hlower.trans_le hratio
  have hexponentPositive : 0 < exponent := by linarith
  have hexponentMinus : 0 < exponent - 1 := by linarith
  have hfirstNonnegative : 0 ≤ firstBound := (abs_nonneg _).trans hfirst
  have htaylorNonnegative : 0 ≤ taylorBound := le_trans (by positivity) htaylorBound
  have hvelocityNonnegative : 0 ≤ velocityBound := le_trans (by positivity) hvelocityBound
  have hexponentNonnegative : 0 ≤ exponentBound := le_trans (by positivity) hexponentBound
  have hdisplacement := centeredAddressDisplacement_bounds verticalDepth tailDepth digits hpositive hless
  have hdisplacementSmall : centeredAddressDisplacement verticalDepth tailDepth digits ratio ∈
      Set.Icc (0 : ℝ) (1 / 2) := ⟨hdisplacement.1, hdisplacement.2.trans hsmall⟩
  have hvelocity := centeredDisplacement_first_polynomial_bound hlower hratio hless
    verticalDepth tailDepth hdepth htail digits hfirst
  have hscale := centered_normalization_exponent_bound hexponentPositive.le
    horizontalDepth verticalDepth hdepth hphase hepsilon
  unfold centeredRemainderFirst
  rw [← mul_assoc (ratio ^ (-exponent * (horizontalDepth : ℝ)))]
  apply centered_first_derivative_envelope hlower hratio verticalDepth
    htaylorNonnegative hvelocityNonnegative hexponentNonnegative hdisplacement.1 hdisplacement.2
  · exact hvelocity.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hvelocityBound (Nat.cast_nonneg _)) (pow_nonneg hpositive.le _))
  · exact hscale.trans (mul_le_mul_of_nonneg_right hexponentBound (Nat.cast_nonneg _))
  · exact (centeredTaylorRemainder_quadratic_bound hexponent hdisplacementSmall).trans
      (mul_le_mul_of_nonneg_right htaylorBound (sq_nonneg _))
  · exact (centeredTaylorFirst_bound hexponent hdisplacementSmall).trans
      (mul_le_mul_of_nonneg_right htaylorBound hdisplacement.1)

/-- Substitute the actual address displacement and Taylor estimates into
the second derivative envelope. The four constants are explicit numerical
majorants, independent of the cylinder depths and digits. -/
theorem centeredRemainderSecond_bound
    {exponent lower ratio target epsilon firstBound secondBound
      taylorBound velocityBound accelerationBound exponentBound : ℝ}
    (hexponent : 1 < exponent) (hlower : 0 < lower) (hratio : lower ≤ ratio) (hless : ratio < 1)
    (horizontalDepth verticalDepth tailDepth : ℕ) (htwo : 2 ≤ verticalDepth)
    (htail : tailDepth ≤ verticalDepth) (digits : ℕ → Bool)
    (hsmall : ratio ^ verticalDepth ≤ 1 / 2)
    (hphase : |(verticalDepth : ℝ) - exponent * horizontalDepth - target| ≤ epsilon)
    (hepsilon : epsilon ≤ 1)
    (hfirst : |deriv (fun parameter => address parameter digits) ratio| ≤ firstBound)
    (hsecond : |deriv (deriv (fun parameter => address parameter digits)) ratio| ≤ secondBound)
    (htaylorBound : exponent * (exponent - 1) * max 1 ((1 / 2 : ℝ) ^ (exponent - 2)) ≤ taylorBound)
    (hvelocityBound : 3 / lower + firstBound ≤ velocityBound)
    (haccelerationBound : 5 / lower ^ 2 + 4 * firstBound / lower + secondBound ≤ accelerationBound)
    (hexponentBound : |target| + 2 ≤ exponentBound) :
    |centeredRemainderSecond exponent horizontalDepth verticalDepth tailDepth digits ratio| ≤
      (exponentBound * (exponentBound + 1) / lower ^ 2 * taylorBound +
        2 * exponentBound / lower * taylorBound * velocityBound +
        taylorBound * velocityBound ^ 2 + taylorBound * accelerationBound) *
          (verticalDepth : ℝ) ^ 2 *
          (ratio ^ (-exponent * (horizontalDepth : ℝ)) * (ratio ^ verticalDepth) ^ 2) := by
  have hpositive := hlower.trans_le hratio
  have hexponentPositive : 0 < exponent := by linarith
  have hexponentMinus : 0 < exponent - 1 := by linarith
  have hfirstNonnegative : 0 ≤ firstBound := (abs_nonneg _).trans hfirst
  have hsecondNonnegative : 0 ≤ secondBound := (abs_nonneg _).trans hsecond
  have htaylorNonnegative : 0 ≤ taylorBound := le_trans (by positivity) htaylorBound
  have hvelocityNonnegative : 0 ≤ velocityBound := le_trans (by positivity) hvelocityBound
  have haccelerationNonnegative : 0 ≤ accelerationBound := le_trans (by positivity) haccelerationBound
  have hexponentNonnegative : 0 ≤ exponentBound := le_trans (by positivity) hexponentBound
  have hdisplacement := centeredAddressDisplacement_bounds verticalDepth tailDepth digits hpositive hless
  have hdisplacementSmall : centeredAddressDisplacement verticalDepth tailDepth digits ratio ∈
      Set.Icc (0 : ℝ) (1 / 2) := ⟨hdisplacement.1, hdisplacement.2.trans hsmall⟩
  have hvelocity := centeredDisplacement_first_polynomial_bound hlower hratio hless
    verticalDepth tailDepth (by omega) htail digits hfirst
  have hacceleration := centeredDisplacement_second_polynomial_bound hlower hratio hless
    verticalDepth tailDepth htwo htail digits hfirst hsecond
  have hscale := centered_normalization_exponent_bound (by linarith : 0 ≤ exponent)
    horizontalDepth verticalDepth (by omega) hphase hepsilon
  unfold centeredRemainderSecond
  apply centered_second_derivative_envelope hlower hratio verticalDepth (by omega)
    htaylorNonnegative hvelocityNonnegative haccelerationNonnegative hexponentNonnegative
    hdisplacement.1 hdisplacement.2
  · apply hvelocity.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hvelocityBound (Nat.cast_nonneg _)) (pow_nonneg hpositive.le _)
  · apply hacceleration.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right haccelerationBound (sq_nonneg _)) (pow_nonneg hpositive.le _)
  · exact hscale.trans (mul_le_mul_of_nonneg_right hexponentBound (Nat.cast_nonneg _))
  · exact (centeredTaylorRemainder_quadratic_bound hexponent hdisplacementSmall).trans
      (mul_le_mul_of_nonneg_right htaylorBound (sq_nonneg _))
  · exact (centeredTaylorFirst_bound hexponent hdisplacementSmall).trans
      (mul_le_mul_of_nonneg_right htaylorBound hdisplacement.1)
  · exact (centeredTaylorSecond_bound hexponent hdisplacementSmall).trans htaylorBound

end LambdaCantor.AE
