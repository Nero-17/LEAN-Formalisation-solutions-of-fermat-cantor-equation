import LambdaCantor.AE.CenteredFactorSecond
import LambdaCantor.AE.CenteredTailLimits

noncomputable section
open Filter
open scoped Topology

namespace LambdaCantor.AE

theorem centeredFactorFirst_tendsto_zero {lower upper : ℝ}
    (lower_positive : 0 < lower) (ordered : lower ≤ upper) (upper_less_one : upper < 1)
    (ratios : ℕ → ℝ) (ratios_mem : ∀ index, ratios index ∈ Set.Icc lower upper)
    (digits : ℕ → ℕ → Bool) :
    Tendsto (fun index => centeredHorizontalFirst index (digits index) (ratios index)) atTop (𝓝 0) ∧
      Tendsto (fun index => centeredDisplacementFirst 0 index (digits index) (ratios index)) atTop (𝓝 0) := by
  have limits := centered_factor_derivatives_tendsto_zero lower_positive ordered upper_less_one ratios ratios_mem digits
  constructor
  · apply limits.1.congr
    exact fun index =>
      (centeredHorizontalFactor_first_actual index (digits index)
        (lower_positive.trans_le (ratios_mem index).1) ((ratios_mem index).2.trans_lt upper_less_one)).deriv
  · apply limits.2.congr
    exact fun index =>
      (centeredTailFactor_first_actual index (digits index)
        (lower_positive.trans_le (ratios_mem index).1) ((ratios_mem index).2.trans_lt upper_less_one)).deriv

/-- Complete horizontal and vertical factors have uniformly vanishing second
derivatives for arbitrary addresses on the fixed compact parameter band. -/
theorem centeredFactorSecond_tendsto_zero {lower upper firstBound secondBound : ℝ}
    (lower_positive : 0 < lower) (ordered : lower ≤ upper) (upper_less_one : upper < 1)
    (ratios : ℕ → ℝ) (ratios_mem : ∀ index, ratios index ∈ Set.Icc lower upper)
    (digits : ℕ → ℕ → Bool)
    (first_bound : ∀ index, |deriv (fun parameter => address parameter (digits index)) (ratios index)| ≤ firstBound)
    (second_bound : ∀ index, |deriv (deriv (fun parameter => address parameter (digits index))) (ratios index)| ≤ secondBound) :
    Tendsto (fun index => centeredHorizontalSecond index (digits index) (ratios index)) atTop (𝓝 0) ∧
      Tendsto (fun index => centeredDisplacementSecond 0 index (digits index) (ratios index)) atTop (𝓝 0) := by
  have upper_nonnegative := lower_positive.le.trans ordered
  have norm_less_one : ‖upper‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg upper_nonnegative]
  have decay : Tendsto (fun index : ℕ => (index : ℝ)^2*upper^index) atTop (𝓝 0) :=
    (summable_pow_mul_geometric_of_norm_lt_one 2 norm_less_one).tendsto_atTop_zero
  have vanishing := decay.const_mul (2/lower^2+2*firstBound/lower+secondBound)
  have estimates : ∀ᶠ index : ℕ in atTop,
      |centeredHorizontalSecond index (digits index) (ratios index)| ≤
        (2/lower^2+2*firstBound/lower+secondBound)*(index : ℝ)^2*upper^index ∧
      |centeredDisplacementSecond 0 index (digits index) (ratios index)| ≤
        (2/lower^2+2*firstBound/lower+secondBound)*(index : ℝ)^2*upper^index := by
    filter_upwards [eventually_ge_atTop 2] with index large
    exact centeredFactorSecond_uniform_bound index large (digits index) lower_positive
      (ratios_mem index).1 (ratios_mem index).2 upper_less_one (first_bound index) (second_bound index)
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq, sub_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (estimates.mono (fun _ estimate => estimate.1))
    simpa only [mul_assoc, mul_zero] using vanishing
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq, sub_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (estimates.mono (fun _ estimate => estimate.2))
    simpa only [mul_assoc, mul_zero] using vanishing

end LambdaCantor.AE
