import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor

/-- Uniform logarithm control on parameters bounded away from zero. -/
theorem log_parameter_lipschitz {lower left right : ℝ}
    (hlower : 0 < lower) (hleft : lower ≤ left) (hright : lower ≤ right) :
    |Real.log right - Real.log left| ≤ lower⁻¹ * |right - left| := by
  have hdifferentiable : ∀ parameter ∈ Set.Ici lower,
      DifferentiableAt ℝ Real.log parameter := by
    intro parameter hparameter
    exact Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le hlower hparameter))
  have hbound : ∀ parameter ∈ Set.Ici lower, ‖deriv Real.log parameter‖ ≤ lower⁻¹ := by
    intro parameter hparameter
    have hpos : 0 < parameter := lt_of_lt_of_le hlower hparameter
    rw [Real.deriv_log, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_le_inv₀ hpos hlower).mpr hparameter
  simpa only [Real.norm_eq_abs] using
    (convex_Ici lower).norm_image_sub_le_of_norm_deriv_le hdifferentiable hbound hleft hright

/-- Exponentially close parameters have asymptotically identical level scales.
This is the parent-child comparability assertion in root-fibres. -/
theorem tendsto_scale_ratio_of_exponential_closeness
    {left right : ℕ → ℝ} {lower upper constant : ℝ}
    (hlower : 0 < lower) (hupper_nonneg : 0 ≤ upper) (hupper : upper < 1)
    (hleft : ∀ index, lower ≤ left index) (hright : ∀ index, lower ≤ right index)
    (hclose : ∀ index, |right index - left index| ≤ constant * upper ^ index) :
    Filter.Tendsto (fun index : ℕ => right index ^ index / left index ^ index)
      Filter.atTop (nhds (1 : ℝ)) := by
  have hlog : ∀ index : ℕ,
      |(index : ℝ) * (Real.log (right index) - Real.log (left index))| ≤
        (lower⁻¹ * constant) * ((index : ℝ) * upper ^ index) := by
    intro index
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (index : ℝ) from Nat.cast_nonneg index)]
    calc
      _ ≤ (index : ℝ) * (lower⁻¹ * |right index - left index|) :=
        mul_le_mul_of_nonneg_left (log_parameter_lipschitz hlower (hleft index) (hright index))
          (Nat.cast_nonneg index)
      _ ≤ (index : ℝ) * (lower⁻¹ * (constant * upper ^ index)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hclose index) (inv_nonneg.mpr hlower.le))
          (Nat.cast_nonneg index)
      _ = _ := by ring
  have hzero : Filter.Tendsto
      (fun index : ℕ => (index : ℝ) * (Real.log (right index) - Real.log (left index)))
      Filter.atTop (nhds (0 : ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
    · intro index
      simpa only [Real.norm_eq_abs] using hlog index
    · simpa using (tendsto_self_mul_const_pow_of_lt_one hupper_nonneg hupper).const_mul
        (lower⁻¹ * constant)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hzero
  convert hexp using 1
  · funext index
    dsimp only [Function.comp_def]
    rw [mul_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (lt_of_lt_of_le hlower (hright index)),
      Real.exp_log (lt_of_lt_of_le hlower (hleft index))]
  · simp

end LambdaCantor


