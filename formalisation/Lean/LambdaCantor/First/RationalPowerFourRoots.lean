import LambdaCantor.First.RationalPowerFourEndpoint
import LambdaCantor.First.RationalNormalizedResidualConvergence
import LambdaCantor.First.Roots
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
namespace LambdaCantor.First

/-- The actual quotient residual is differentiable throughout the positive
parameter interval; division is safe because its cylinder scale is nonzero. -/
theorem differentiableAt_powersFourNormalizedResidual (exponent phase index : ℕ)
    (leftDigits rightDigits : ℕ → Bool) {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    DifferentiableAt ℝ (powersFourNormalizedResidual exponent phase index leftDigits rightDigits) ratio := by
  have hleft := (((hasDerivAt_id ratio).pow index).mul
    (hasDerivAt_powersFourLeftFactor hpos hlt
      (exponent * index + phase + phase + 2) leftDigits)).pow exponent
  have hright := (((hasDerivAt_const ratio (1 : ℝ)).sub
    ((hasDerivAt_id ratio).pow (exponent * index + phase))).add
      (((hasDerivAt_id ratio).pow
        ((exponent * index + phase) + (exponent * index + phase + phase + 2))).mul
          (hasDerivAt_address_parameter hpos hlt rightDigits))).pow exponent
  exact ((hleft.add hright).sub_const 1).differentiableAt.div
    ((hasDerivAt_id ratio).pow (exponent * index)).differentiableAt (pow_ne_zero _ (ne_of_gt hpos))

/-- At every fixed parameter strictly above one quarter, the limiting
powers-four polynomial is strictly negative. -/
theorem powersFour_limiting_polynomial_neg (phase : ℕ) (hphase : 1 ≤ phase)
    {ratio : ℝ} (hratio : (1 / 4 : ℝ) < ratio) :
    1 - ((4 ^ phase : ℕ) : ℝ) * ratio ^ phase < 0 := by
  have hpower := one_lt_pow₀ (show (1 : ℝ) < 4 * ratio by linarith)
    (show phase ≠ 0 by omega)
  rw [mul_pow] at hpower
  push_cast
  linarith

/-- For every positive phase, every pair of binary tails has a unique root
strictly between one quarter and any fixed upper parameter below one half,
once the cylinder index is sufficiently large. All analytic hypotheses have
been discharged for the actual normalized cylinder residual. -/
theorem eventually_powersFour_full_tail_unique_root
    (phase : ℕ) (hphase : 1 ≤ phase) {upper : ℝ}
    (hupperLower : (1 / 4 : ℝ) < upper) (hupper : upper < 1 / 2) :
    ∀ᶠ index : ℕ in Filter.atTop, ∀ leftDigits rightDigits : ℕ → Bool,
      ∃! ratio : ℝ, ratio ∈ Set.Ioo (1 / 4 : ℝ) upper ∧
        powersFourNormalizedResidual (4 ^ phase) phase index leftDigits rightDigits ratio = 0 := by
  have hexponent : 2 ≤ (4 : ℕ) ^ phase := by
    have hfour : 4 ≤ (4 : ℕ) ^ phase := by
      simpa using pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℕ)) hphase
    omega
  have hupperOne : upper < 1 := by linarith
  have hvalue := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_powersFourNormalizedResidual (4 ^ phase) phase hexponent
      (by norm_num : (0 : ℝ) < 1 / 4) hupperOne hupperLower.le)
  have hderivative := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_powersFourNormalizedResidual_derivative (4 ^ phase) phase hexponent
      (by norm_num : (0 : ℝ) < 1 / 4) hupperOne hupperLower.le)
  have hnegative := powersFour_limiting_polynomial_neg phase hphase hupperLower
  have hphaseReal : (0 : ℝ) < phase := by exact_mod_cast (show 0 < phase by omega)
  have hslope : 0 < ((4 ^ phase : ℕ) : ℝ) * (phase : ℝ) * (1 / 4 : ℝ) ^ (phase - 1) / 2 := by
    positivity
  filter_upwards [hvalue (-(1 - ((4 ^ phase : ℕ) : ℝ) * upper ^ phase) / 2) (by linarith),
    hderivative (((4 ^ phase : ℕ) : ℝ) * (phase : ℝ) * (1 / 4 : ℝ) ^ (phase - 1) / 2) hslope,
    Filter.eventually_ge_atTop (1 : ℕ)] with index hvalueIndex hderivativeIndex hindex
  intro leftDigits rightDigits
  have hcontinuous : ContinuousOn
      (powersFourNormalizedResidual (4 ^ phase) phase index leftDigits rightDigits)
      (Set.Icc (1 / 4 : ℝ) upper) := by
    intro ratio hratio
    exact (differentiableAt_powersFourNormalizedResidual (4 ^ phase) phase index leftDigits rightDigits
      (by linarith [hratio.1]) (hratio.2.trans_lt hupperOne)).continuousAt.continuousWithinAt
  have hderivativeBound : ∀ ratio ∈ Set.Ioo (1 / 4 : ℝ) upper,
      deriv (powersFourNormalizedResidual (4 ^ phase) phase index leftDigits rightDigits) ratio ≤
        -(((4 ^ phase : ℕ) : ℝ) * (phase : ℝ) * (1 / 4 : ℝ) ^ (phase - 1) / 2) := by
    intro ratio hratio
    have hbound := hderivativeIndex
      (⟨ratio, ⟨hratio.1.le, hratio.2.le⟩⟩, (leftDigits, rightDigits))
    rw [Real.dist_eq] at hbound
    have herror := (abs_lt.mp hbound).1
    have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      hratio.1.le (phase - 1)
    have hcoefficient := mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ ((4 ^ phase : ℕ) : ℝ) * (phase : ℝ) by positivity)
    dsimp only at herror
    nlinarith
  have hright : powersFourNormalizedResidual (4 ^ phase) phase index leftDigits rightDigits upper < 0 := by
    have hbound := hvalueIndex (⟨upper, ⟨hupperLower.le, le_rfl⟩⟩, (leftDigits, rightDigits))
    rw [Real.dist_eq] at hbound
    have herror := (abs_lt.mp hbound).1
    dsimp only at herror
    linarith
  exact Roots.unique_interior_root hupperLower hcontinuous
    (LambdaCantor.strictAntiOn_of_uniform_negative_derivative hcontinuous hslope hderivativeBound)
    (powersFourNormalizedResidual_quarter_pos phase index hphase hindex leftDigits rightDigits) hright

end LambdaCantor.First


