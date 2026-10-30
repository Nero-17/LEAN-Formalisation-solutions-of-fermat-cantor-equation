import LambdaCantor.Last.AnalyticCoarseLargeSecant
import LambdaCantor.Last.AnalyticCoarseNumericLogs
import Mathlib.Data.Nat.Find

noncomputable section
namespace LambdaCantor.Last

def largeSecantScale (exponent ratio period : ℝ) (depth : ℕ) : ℝ :=
  exponent*Real.log (1+ratio^depth/(1-ratio))/period

theorem large_secant_scale_next_lower {exponent ratio period : ℝ} (depth : ℕ)
    (exponent_nonnegative : 0 ≤ exponent) (ratio_positive : 0 < ratio)
    (ratio_less_one : ratio < 1) (period_positive : 0 < period) :
    ratio*largeSecantScale exponent ratio period depth ≤
      largeSecantScale exponent ratio period (depth+1) := by
  have relative_nonnegative : 0 ≤ ratio^depth/(1-ratio) :=
    div_nonneg (pow_nonneg ratio_positive.le _) (by linarith)
  have concavity := (log_secant_error_bounds relative_nonnegative
    (show ratio ∈ Set.Icc (0 : ℝ) 1 from ⟨ratio_positive.le, ratio_less_one.le⟩)).1
  have next_identity : ratio^(depth+1)/(1-ratio) = (ratio^depth/(1-ratio))*ratio := by
    rw [pow_succ]
    ring
  unfold largeSecantScale
  rw [next_identity]
  have multiplied := mul_le_mul_of_nonneg_left concavity
    (div_nonneg exponent_nonnegative period_positive.le)
  have normalized : exponent / period *
      (Real.log (1 + ratio ^ depth / (1 - ratio) * ratio) -
        ratio * Real.log (1 + ratio ^ depth / (1 - ratio))) =
      exponent * Real.log (1 + ratio ^ depth / (1 - ratio) * ratio) / period -
        ratio * (exponent * Real.log (1 + ratio ^ depth / (1 - ratio)) / period) := by
    ring
  rw [mul_zero, normalized] at multiplied
  exact sub_nonneg.mp multiplied

/-- Selects the last consecutive depth before the secant scale drops below
one. The upper bound β<1/λ follows from the proved logarithmic concavity,
not from an assumed scale-selection property. -/
theorem exists_large_secant_scale {exponent ratio period : ℝ}
    (exponent_positive : 0 < exponent) (ratio_positive : 0 < ratio)
    (ratio_less_one : ratio < 1) (period_positive : 0 < period)
    (initial_scale : 1 ≤ largeSecantScale exponent ratio period 1) :
    ∃ depth : ℕ, 1 ≤ depth ∧
      1 ≤ largeSecantScale exponent ratio period depth ∧
      largeSecantScale exponent ratio period (depth+1) < 1 ∧
      largeSecantScale exponent ratio period depth < 1/ratio := by
  classical
  have complement_positive : 0 < 1-ratio := by linarith
  obtain ⟨cutoff, power_small⟩ := exists_pow_lt_of_lt_one
    (div_pos (mul_pos complement_positive period_positive) exponent_positive) ratio_less_one
  have eventual_small : ∃ index : ℕ, largeSecantScale exponent ratio period (index+1) < 1 := by
    refine ⟨cutoff, ?_⟩
    have next_power_bound : ratio^(cutoff+1) ≤ ratio^cutoff :=
      pow_le_pow_of_le_one ratio_positive.le ratio_less_one.le (by omega)
    have next_power_small : ratio^(cutoff+1) < (1-ratio)*period/exponent :=
      next_power_bound.trans_lt power_small
    have relative_nonnegative : 0 ≤ ratio^(cutoff+1)/(1-ratio) :=
      div_nonneg (pow_nonneg ratio_positive.le _) complement_positive.le
    have log_bound : Real.log (1+ratio^(cutoff+1)/(1-ratio)) ≤ ratio^(cutoff+1)/(1-ratio) := by
      have bound := Real.log_le_sub_one_of_pos (show 0 < 1+ratio^(cutoff+1)/(1-ratio) by linarith)
      linarith
    have product_small : exponent*ratio^(cutoff+1) < (1-ratio)*period := by
      have bound := (lt_div_iff₀ exponent_positive).mp next_power_small
      nlinarith
    have quotient_small : exponent*(ratio^(cutoff+1)/(1-ratio)) < period := by
      rw [← mul_div_assoc]
      exact (div_lt_iff₀ complement_positive).mpr (by nlinarith)
    unfold largeSecantScale
    apply (div_lt_one period_positive).mpr
    exact (mul_le_mul_of_nonneg_left log_bound exponent_positive.le).trans_lt quotient_small
  let depth := Nat.find eventual_small
  have next_small : largeSecantScale exponent ratio period (depth+1) < 1 := Nat.find_spec eventual_small
  have depth_positive : 0 < depth := by
    by_contra failure
    have zero : depth = 0 := by omega
    rw [zero] at next_small
    norm_num only [zero_add] at next_small
    linarith
  have current_large : 1 ≤ largeSecantScale exponent ratio period depth := by
    have previous : depth-1 < Nat.find eventual_small := by change depth-1 < depth; omega
    have not_small := Nat.find_min eventual_small previous
    have previous_identity : depth-1+1 = depth := by omega
    rw [previous_identity] at not_small
    exact le_of_not_gt not_small
  have next_lower := large_secant_scale_next_lower depth exponent_positive.le ratio_positive
    ratio_less_one period_positive
  refine ⟨depth, by omega, current_large, next_small, ?_⟩
  exact (lt_div_iff₀ ratio_positive).mpr (by nlinarith)

/-- The genuine logarithmic hull and period bounds ensure the required
initial scale for every exponent at least twenty. -/
theorem exists_large_secant_scale_of_twenty {exponent ratio : ℝ}
    (exponent_lower : 20 ≤ exponent) (ratio_lower : 183/500 ≤ ratio) (ratio_upper : ratio < 1/2) :
    ∃ depth : ℕ, 1 ≤ depth ∧
      1 ≤ largeSecantScale exponent ratio (-Real.log ratio) depth ∧
      largeSecantScale exponent ratio (-Real.log ratio) (depth+1) < 1 ∧
      largeSecantScale exponent ratio (-Real.log ratio) depth < 1/ratio := by
  have ratio_positive : 0 < ratio := by linarith
  have ratio_less_one : ratio < 1 := by linarith
  have complement_positive : 0 < 1-ratio := by linarith
  have period_positive : 0 < -Real.log ratio := neg_pos.mpr (Real.log_neg ratio_positive ratio_less_one)
  have basic_bounds := coarse_log_hull_period_bounds ratio_lower ratio_upper
  have argument_identity : 1+ratio/(1-ratio) = (1-ratio)⁻¹ := by
    field_simp [complement_positive.ne']
    <;> ring
  have initial_identity : largeSecantScale exponent ratio (-Real.log ratio) 1 =
      exponent*((-Real.log (1-ratio))/(-Real.log ratio)) := by
    unfold largeSecantScale
    rw [pow_one, argument_identity, Real.log_inv]
    ring
  apply exists_large_secant_scale (by linarith) ratio_positive ratio_less_one period_positive
  rw [initial_identity]
  nlinarith [basic_bounds.2.2.1]

end LambdaCantor.Last
