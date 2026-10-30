import LambdaCantor.AE.CenteredMixedScale
import LambdaCantor.AE.CenteredWindowPower

noncomputable section
open Filter
open scoped Topology

namespace LambdaCantor.AE

/-- The actual phase and exponential depth choices imply a uniform mixed
parameter/tail bound. No derivative-prefix estimate is assumed here. -/
theorem centered_uniform_mixed_bound {exponent center lower upper width target : ℝ}
    (exponent_greater_one : 1 < exponent) (center_positive : 0 < center) (center_less_one : center < 1)
    (lower_positive : 0 < lower) (ordered : lower ≤ upper) (upper_less_one : upper < 1)
    (width_nonnegative : 0 ≤ width) (horizontalDepth verticalDepth : ℕ → ℕ)
    (depths : ∀ index, index ≤ verticalDepth index ∧ 1 ≤ verticalDepth index)
    (phase : ∀ index, |(verticalDepth index : ℝ)-exponent*horizontalDepth index-target| ≤ (center^index)^2)
    (decay : ∀ index, (verticalDepth index : ℝ)^2*upper^verticalDepth index ≤ (center^index)^3) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ᶠ index : ℕ in atTop,
      ∀ depth first second ratio, ratio ∈ Set.Icc lower upper → |ratio-center| ≤ width*center^index →
        (∀ position < depth, first position = second position) →
        |deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index first) ratio -
          deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index second) ratio| ≤
          constant*center^index*(((index+depth+1 : ℕ) : ℝ))*upper^depth := by
  let discrepancyBound := |target|+1
  let resonanceBound := lower^(-(|target|+1))
  let exponentBound := |target|+2
  let constant := 2*centeredMixedConstant exponent lower upper discrepancyBound resonanceBound exponentBound resonanceBound+1
  have exponent_positive : 0 < exponent := by linarith
  have exponent_minus_positive : 0 < exponent-1 := sub_pos.mpr exponent_greater_one
  have upper_positive : 0 < upper := lower_positive.trans_le ordered
  have address_nonnegative : 0 ≤ addressParameterDerivativeBound upper :=
    (abs_nonneg _).trans (address_parameter_derivative_bound lower_positive.le ordered upper_less_one (fun _ => false))
  have resonance_positive : 0 < resonanceBound := Real.rpow_pos_of_pos lower_positive _
  have mixed_nonnegative :
      0 ≤ centeredMixedConstant exponent lower upper discrepancyBound resonanceBound exponentBound resonanceBound := by
    unfold centeredMixedConstant
    dsimp [discrepancyBound, exponentBound]
    positivity
  have constant_positive : 0 < constant := by dsimp [constant]; linarith
  refine ⟨constant, constant_positive, ?_⟩
  have comparable := centered_window_power_comparable center_positive center_less_one width_nonnegative
  have power_small : ∀ᶠ index : ℕ in atTop, upper^index < (1/2 : ℝ) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (lower_positive.le.trans ordered) upper_less_one).eventually
      (gt_mem_nhds (by norm_num))
  filter_upwards [comparable, power_small] with index comparable power_small
  intro depth first second ratio ratio_mem distance agreement
  have positive := lower_positive.trans_le ratio_mem.1
  have less_one := ratio_mem.2.trans_lt upper_less_one
  have center_power_one : center^index ≤ 1 := pow_le_one₀ center_positive.le center_less_one.le
  have epsilon_one : (center^index)^2 ≤ 1 := pow_le_one₀ (pow_nonneg center_positive.le _) center_power_one
  have phase_absolute : |(verticalDepth index : ℝ)-exponent*horizontalDepth index| ≤ discrepancyBound := by
    calc
      _ = |((verticalDepth index : ℝ)-exponent*horizontalDepth index-target)+target| := by congr 1; ring
      _ ≤ |(verticalDepth index : ℝ)-exponent*horizontalDepth index-target|+|target| := abs_add_le _ _
      _ ≤ discrepancyBound := by dsimp [discrepancyBound]; linarith [phase index]
  have resonance : ratio^((verticalDepth index : ℝ)-exponent*horizontalDepth index) ≤ resonanceBound := by
    apply centered_resonance_factor_bound lower_positive ratio_mem.1 less_one.le (by positivity)
    exact (abs_le.mp phase_absolute).1
  have scale := centered_normalization_exponent_bound exponent_positive.le (horizontalDepth index) (verticalDepth index)
    (depths index).2 (phase index) epsilon_one
  have normalized := centered_normalized_quadratic_decay lower_positive ratio_mem.1 ratio_mem.2 upper_less_one
    (horizontalDepth index) (verticalDepth index) (phase index) epsilon_one (decay index)
  have normalized_bound : (verticalDepth index : ℝ)^2*
      (ratio^(-exponent*(horizontalDepth index : ℝ))*(ratio^verticalDepth index)^2) ≤ resonanceBound := by
    apply normalized.trans
    exact mul_le_of_le_one_right resonance_positive.le
      (pow_le_one₀ (pow_nonneg center_positive.le _) center_power_one)
  have tail_small : ratio^index ≤ 1/2 := (pow_le_pow_left₀ positive.le ratio_mem.2 _).trans power_small.le
  have vertical_small : ratio^verticalDepth index ≤ 1/2 :=
    ((pow_le_pow_left₀ positive.le ratio_mem.2 _).trans
      (pow_le_pow_of_le_one (lower_positive.le.trans ordered) upper_less_one.le (depths index).1)).trans power_small.le
  have bound := centeredNormalizedResidual_first_prefix_rho_bound exponent_greater_one lower_positive ratio_mem.1 ratio_mem.2
    upper_less_one (pow_nonneg center_positive.le index) (horizontalDepth index) (verticalDepth index) index depth
    (depths index).2 (depths index).1 tail_small vertical_small (comparable ratio distance).2
    phase_absolute resonance (by positivity) scale normalized_bound first second agreement
  apply bound.trans
  have coefficient : 2*centeredMixedConstant exponent lower upper discrepancyBound resonanceBound exponentBound resonanceBound ≤ constant := by
    dsimp [constant]
    linarith
  have enlarged := mul_le_mul_of_nonneg_right coefficient
    (show 0 ≤ center^index*(((index+depth+1 : ℕ) : ℝ))*upper^depth by positivity)
  simpa only [mul_assoc] using enlarged

end LambdaCantor.AE
