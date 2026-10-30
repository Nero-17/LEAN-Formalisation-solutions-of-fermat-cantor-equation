import LambdaCantor.First.RationalNormalizedResidual
import LambdaCantor.First.RationalPowerFour
import LambdaCantor.First.RationalEstimates

noncomputable section
namespace LambdaCantor.First

/-- Strict polynomial positivity from curvature and the prescribed full-tail
padding. This is the quantitative quarter-endpoint calculation. -/
theorem powersFour_polynomial_endpoint_positive (exponent : ℕ) (hexponent : 4 ≤ exponent)
    {scale paddingScale : ℝ} (hscale : 0 < scale) (hscaleOne : scale ≤ 1)
    (hpadding : 0 ≤ paddingScale) (hpaddingOne : paddingScale ≤ 1)
    (hsmall : ((exponent - 2 : ℕ) : ℝ) * scale < 1 / 2)
    (hloss : (exponent : ℝ) * paddingScale ≤ scale / 16) :
    0 < ((exponent : ℝ) * scale) * (1 - paddingScale) ^ exponent +
      (1 - scale) ^ exponent - 1 := by
  have hnat : exponent - 2 + 2 = exponent := by omega
  have hcast : ((exponent - 2 : ℕ) : ℝ) + 2 = (exponent : ℝ) := by exact_mod_cast hnat
  have hcurvature := normalized_curvature_strict_lower (exponent - 2) hscale hscaleOne hsmall
  rw [hnat, hcast] at hcurvature
  have hcoefficient : ((exponent - 2 : ℕ) : ℝ) + 1 = (exponent : ℝ) - 1 := by linarith
  rw [hcoefficient] at hcurvature
  have hexponentPositive : (0 : ℝ) < exponent := by exact_mod_cast (show 0 < exponent by omega)
  have hdenominator : 0 < (exponent : ℝ) * scale := by positivity
  have hcurvatureNumerator := (lt_div_iff₀ hdenominator).mp hcurvature
  have hbernoulli := one_add_mul_le_pow (a := -paddingScale) (by linarith) exponent
  have hbase : 1 + -paddingScale = 1 - paddingScale := by ring
  rw [hbase] at hbernoulli
  have hlower := mul_le_mul_of_nonneg_left hbernoulli hdenominator.le
  have hexponentReal : (4 : ℝ) ≤ exponent := by exact_mod_cast hexponent
  have hgap : 0 < (exponent : ℝ) * scale *
      (((exponent : ℝ) - 1) / 4 * scale - (exponent : ℝ) * paddingScale) := by
    apply mul_pos hdenominator
    nlinarith
  nlinarith

/-- Every pair of full binary tails has strictly positive normalized residual
at one quarter, for powers-four exponents and every positive cylinder index. -/
theorem powersFourNormalizedResidual_quarter_pos (phase index : ℕ)
    (hphase : 1 ≤ phase) (hindex : 1 ≤ index) (leftDigits rightDigits : ℕ → Bool) :
    0 < powersFourNormalizedResidual (4 ^ phase) phase index leftDigits rightDigits (1 / 4) := by
  have hexponent : 4 ≤ (4 : ℕ) ^ phase := by
    simpa using pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℕ)) hphase
  have hsmall := powers_four_curvature_smallness phase index hphase hindex
  have hloss := powers_four_tail_loss phase (4 ^ phase * index + phase)
  have hpolynomial := powersFour_polynomial_endpoint_positive (4 ^ phase) hexponent
    (scale := (1 / 4 : ℝ) ^ (4 ^ phase * index + phase))
    (paddingScale := (1 / 4 : ℝ) ^ (4 ^ phase * index + phase + phase + 2))
    (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
    (by linarith) (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hloss.le)
  have hcancel : ((4 ^ phase : ℕ) : ℝ) * (1 / 4 : ℝ) ^ phase = 1 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using powers_four_cancellation phase
  have hscale : ((4 ^ phase : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (4 ^ phase * index + phase) =
      (1 / 4 : ℝ) ^ (4 ^ phase * index) := by
    rw [pow_add]
    calc
      _ = (((4 ^ phase : ℕ) : ℝ) * (1 / 4 : ℝ) ^ phase) *
        (1 / 4 : ℝ) ^ (4 ^ phase * index) := by ring
      _ = _ := by rw [hcancel]; ring
  rw [hscale] at hpolynomial
  have hleftAddress := address_nonnegative (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) leftDigits
  have hrightAddress := address_nonnegative (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) rightDigits
  have hpaddingOne : (1 / 4 : ℝ) ^ (4 ^ phase * index + phase + phase + 2) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hscaleOne : (1 / 4 : ℝ) ^ (4 ^ phase * index + phase) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hleft :
      ((1 / 4 : ℝ) ^ index * (1 - (1 / 4 : ℝ) ^ (4 ^ phase * index + phase + phase + 2))) ^ (4 ^ phase) ≤
      ((1 / 4 : ℝ) ^ index * powersFourLeftFactor (4 ^ phase * index + phase + phase + 2)
        leftDigits (1 / 4)) ^ (4 ^ phase) := by
    apply pow_le_pow_left₀ (mul_nonneg (by positivity) (by linarith))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold powersFourLeftFactor
    nlinarith [mul_nonneg (show 0 ≤ (1 / 4 : ℝ) ^ (4 ^ phase * index + phase + phase + 2) by positivity)
      hleftAddress]
  have hright : (1 - (1 / 4 : ℝ) ^ (4 ^ phase * index + phase)) ^ (4 ^ phase) ≤
      (1 - (1 / 4 : ℝ) ^ (4 ^ phase * index + phase) +
        (1 / 4 : ℝ) ^ ((4 ^ phase * index + phase) + (4 ^ phase * index + phase + phase + 2)) *
          address (1 / 4) rightDigits) ^ (4 ^ phase) := by
    apply pow_le_pow_left₀ (by linarith)
    linarith [mul_nonneg (show 0 ≤ (1 / 4 : ℝ) ^
      ((4 ^ phase * index + phase) + (4 ^ phase * index + phase + phase + 2)) by positivity) hrightAddress]
  rw [mul_pow, ← pow_mul, Nat.mul_comm index (4 ^ phase)] at hleft
  unfold powersFourNormalizedResidual
  apply div_pos _ (by positivity)
  linarith

end LambdaCantor.First

