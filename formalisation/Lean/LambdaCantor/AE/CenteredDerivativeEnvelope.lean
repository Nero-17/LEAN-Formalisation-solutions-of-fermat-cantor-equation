import LambdaCantor.AE.CenteredResonance
import LambdaCantor.AE.CenteredNormalizedBounds
import Mathlib.Tactic.GCongr

noncomputable section
namespace LambdaCantor.AE

/-- The product rule preserves the small quadratic exponential factor.
All constants here are independent of the chosen cylinder depths. -/
theorem centered_first_derivative_envelope
    {lower ratio exponent scaleExponent displacement velocity
      taylorBound velocityBound exponentBound : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (depth : ℕ)
    (htaylor : 0 ≤ taylorBound) (hvelocityBound : 0 ≤ velocityBound)
    (hexponentBound : 0 ≤ exponentBound)
    (hdisplacement : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ ratio ^ depth)
    (hvelocity : |velocity| ≤ velocityBound * (depth : ℝ) * ratio ^ depth)
    (hscale : |scaleExponent| ≤ exponentBound * depth)
    (hremainder : |centeredTaylorRemainder exponent displacement| ≤ taylorBound * displacement ^ 2)
    (hfirst : |centeredTaylorFirst exponent displacement| ≤ taylorBound * displacement) :
    |scaleExponent * ratio ^ (scaleExponent - 1) * centeredTaylorRemainder exponent displacement +
        ratio ^ scaleExponent * centeredTaylorFirst exponent displacement * velocity| ≤
      (exponentBound / lower * taylorBound + taylorBound * velocityBound) *
        (depth : ℝ) * (ratio ^ scaleExponent * (ratio ^ depth) ^ 2) := by
  have hpositive := hlower.trans_le hratio
  have hpower : ratio ^ (scaleExponent - 1) ≤ ratio ^ scaleExponent / lower := by
    simpa using centered_shifted_normalization_bound hlower hratio 1
  have hdisplacementSquare := pow_le_pow_left₀ hdisplacement hdisplacementUpper 2
  calc
    _ ≤ |scaleExponent| * ratio ^ (scaleExponent - 1) * (taylorBound * displacement ^ 2) +
        ratio ^ scaleExponent * (taylorBound * displacement) * |velocity| :=
      centeredNormalizedRemainder_first_bound hpositive hremainder hfirst
    _ ≤ (exponentBound * (depth : ℝ)) * (ratio ^ scaleExponent / lower) *
          (taylorBound * (ratio ^ depth) ^ 2) +
        ratio ^ scaleExponent * (taylorBound * ratio ^ depth) *
          (velocityBound * (depth : ℝ) * ratio ^ depth) := by
      gcongr ?_ * ?_ * (taylorBound * ?_) +
        ratio ^ scaleExponent * (taylorBound * ?_) * ?_ <;> assumption
    _ = _ := by ring

theorem centered_scale_second_coefficient_bound {scaleExponent exponentBound : ℝ}
    (hexponentBound : 0 ≤ exponentBound) (depth : ℕ) (hdepth : 1 ≤ depth)
    (hscale : |scaleExponent| ≤ exponentBound * depth) :
    |scaleExponent * (scaleExponent - 1)| ≤
      exponentBound * (exponentBound + 1) * (depth : ℝ) ^ 2 := by
  have hdepthReal : (1 : ℝ) ≤ depth := by exact_mod_cast hdepth
  have hshift : |scaleExponent - 1| ≤ (exponentBound + 1) * depth := by
    apply (abs_sub _ _).trans
    simp only [abs_one]
    nlinarith
  rw [abs_mul]
  calc
    _ ≤ (exponentBound * (depth : ℝ)) * ((exponentBound + 1) * depth) :=
      mul_le_mul hscale hshift (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem centered_second_derivative_envelope
    {lower ratio exponent scaleExponent displacement velocity acceleration
      taylorBound velocityBound accelerationBound exponentBound : ℝ}
    (hlower : 0 < lower) (hratio : lower ≤ ratio) (depth : ℕ) (hdepth : 1 ≤ depth)
    (htaylor : 0 ≤ taylorBound) (hvelocityBound : 0 ≤ velocityBound)
    (haccelerationBound : 0 ≤ accelerationBound) (hexponentBound : 0 ≤ exponentBound)
    (hdisplacement : 0 ≤ displacement) (hdisplacementUpper : displacement ≤ ratio ^ depth)
    (hvelocity : |velocity| ≤ velocityBound * (depth : ℝ) * ratio ^ depth)
    (hacceleration : |acceleration| ≤ accelerationBound * (depth : ℝ) ^ 2 * ratio ^ depth)
    (hscale : |scaleExponent| ≤ exponentBound * depth)
    (hremainder : |centeredTaylorRemainder exponent displacement| ≤ taylorBound * displacement ^ 2)
    (hfirst : |centeredTaylorFirst exponent displacement| ≤ taylorBound * displacement)
    (hsecond : |centeredTaylorSecond exponent displacement| ≤ taylorBound) :
    |scaleExponent * (scaleExponent - 1) * ratio ^ (scaleExponent - 2) *
        centeredTaylorRemainder exponent displacement +
      2 * scaleExponent * ratio ^ (scaleExponent - 1) *
        centeredTaylorFirst exponent displacement * velocity +
      ratio ^ scaleExponent * (centeredTaylorSecond exponent displacement * velocity ^ 2 +
        centeredTaylorFirst exponent displacement * acceleration)| ≤
      (exponentBound * (exponentBound + 1) / lower ^ 2 * taylorBound +
        2 * exponentBound / lower * taylorBound * velocityBound +
        taylorBound * velocityBound ^ 2 + taylorBound * accelerationBound) *
          (depth : ℝ) ^ 2 * (ratio ^ scaleExponent * (ratio ^ depth) ^ 2) := by
  have hpositive := hlower.trans_le hratio
  have hpowerFirst : ratio ^ (scaleExponent - 1) ≤ ratio ^ scaleExponent / lower := by
    simpa using centered_shifted_normalization_bound hlower hratio 1
  have hpowerSecond : ratio ^ (scaleExponent - 2) ≤ ratio ^ scaleExponent / lower ^ 2 := by
    simpa using centered_shifted_normalization_bound hlower hratio 2
  have hscaleSecond := centered_scale_second_coefficient_bound hexponentBound depth hdepth hscale
  have hdisplacementSquare := pow_le_pow_left₀ hdisplacement hdisplacementUpper 2
  have hvelocitySquare : velocity ^ 2 ≤ (velocityBound * (depth : ℝ) * ratio ^ depth) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg velocity) hvelocity 2
  calc
    _ ≤ |scaleExponent * (scaleExponent - 1)| * ratio ^ (scaleExponent - 2) *
          (taylorBound * displacement ^ 2) +
        2 * |scaleExponent| * ratio ^ (scaleExponent - 1) * (taylorBound * displacement) * |velocity| +
        ratio ^ scaleExponent * (taylorBound * velocity ^ 2 + taylorBound * displacement * |acceleration|) :=
      centeredNormalizedRemainder_second_bound hpositive hremainder hfirst hsecond
    _ ≤ (exponentBound * (exponentBound + 1) * (depth : ℝ) ^ 2) *
          (ratio ^ scaleExponent / lower ^ 2) * (taylorBound * (ratio ^ depth) ^ 2) +
        2 * (exponentBound * (depth : ℝ)) * (ratio ^ scaleExponent / lower) *
          (taylorBound * ratio ^ depth) * (velocityBound * (depth : ℝ) * ratio ^ depth) +
        ratio ^ scaleExponent *
          (taylorBound * (velocityBound * (depth : ℝ) * ratio ^ depth) ^ 2 +
            taylorBound * ratio ^ depth * (accelerationBound * (depth : ℝ) ^ 2 * ratio ^ depth)) := by
      gcongr ?_ * ?_ * (taylorBound * ?_) +
        2 * ?_ * ?_ * (taylorBound * ?_) * ?_ +
        ratio ^ scaleExponent * (taylorBound * ?_ + taylorBound * ?_ * ?_) <;> assumption
    _ = _ := by ring

end LambdaCantor.AE
