import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology
namespace LambdaCantor.AE

/-- Every fixed neighbourhood eventually contains the entire exponentially
shrinking centred parameter window. -/
theorem centered_window_eventually_mem_nhds {centre windowConstant : ℝ}
    (centre_positive : 0 < centre) (centre_less_one : centre < 1)
    {neighbourhood : Set ℝ} (neighbourhood_mem : neighbourhood ∈ 𝓝 centre) :
    ∀ᶠ length : ℕ in atTop, ∀ ratio : ℝ,
      |ratio-centre| ≤ windowConstant*centre^length → ratio ∈ neighbourhood := by
  obtain ⟨radius, radius_positive, ball_subset⟩ := Metric.mem_nhds_iff.mp neighbourhood_mem
  have window_zero : Tendsto (fun length : ℕ => windowConstant*centre^length) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one centre_positive.le centre_less_one).const_mul windowConstant
  filter_upwards [window_zero.eventually (gt_mem_nhds radius_positive)] with length window_small
  intro ratio ratio_window
  apply ball_subset
  rw [Metric.mem_ball, Real.dist_eq]
  exact ratio_window.trans_lt window_small

/-- The derivative majorant for powers decays on every fixed compact interval
strictly below one. -/
theorem centered_window_power_derivative_tendsto_zero {upper : ℝ}
    (upper_positive : 0 < upper) (upper_less_one : upper < 1) :
    Tendsto (fun length : ℕ => (length:ℝ)*upper^(length-1)) atTop (𝓝 0) := by
  have limit := (tendsto_self_mul_const_pow_of_lt_one upper_positive.le upper_less_one).div_const upper
  convert limit using 1
  · funext length
    by_cases zero_length : length = 0
    · simp [zero_length]
    · have length_identity : length-1+1 = length := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero_length)
      have power_identity : upper^length = upper^(length-1)*upper := by
        rw [← pow_succ, length_identity]
      rw [power_identity]
      field_simp [upper_positive.ne']
  · simp

/-- Uniform relative power error on the actual window of width centre^length.
This is stronger than fixed multiplicative comparability. -/
theorem centered_window_power_relative_error {centre windowConstant : ℝ}
    (centre_positive : 0 < centre) (centre_less_one : centre < 1)
    (window_nonnegative : 0 ≤ windowConstant) {epsilon : ℝ} (epsilon_positive : 0 < epsilon) :
    ∀ᶠ length : ℕ in atTop, ∀ ratio : ℝ,
      |ratio-centre| ≤ windowConstant*centre^length →
      |ratio^length-centre^length| ≤ epsilon*centre^length := by
  obtain ⟨upper, centre_upper, upper_less_one⟩ := exists_between centre_less_one
  have upper_positive : 0 < upper := centre_positive.trans centre_upper
  have factor_zero : Tendsto (fun length : ℕ => windowConstant*((length:ℝ)*upper^(length-1))) atTop (𝓝 0) := by
    simpa using (centered_window_power_derivative_tendsto_zero upper_positive upper_less_one).const_mul windowConstant
  have window_inside := centered_window_eventually_mem_nhds
    (windowConstant := windowConstant) centre_positive centre_less_one (Ioo_mem_nhds centre_positive centre_upper)
  filter_upwards [window_inside, factor_zero.eventually (gt_mem_nhds epsilon_positive)]
    with length inside factor_small
  intro ratio ratio_window
  have ratio_bounds := inside ratio ratio_window
  have maximum_bound : max |ratio| |centre| ≤ upper := by
    rw [abs_of_pos ratio_bounds.1, abs_of_pos centre_positive]
    exact max_le ratio_bounds.2.le centre_upper.le
  calc
    |ratio^length-centre^length| ≤ |ratio-centre| * (length:ℝ)*max |ratio| |centre|^(length-1) :=
      abs_pow_sub_pow_le ratio centre length
    _ ≤ (windowConstant*centre^length)*(length:ℝ)*upper^(length-1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right ratio_window (Nat.cast_nonneg length)
      · exact pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg ratio)) maximum_bound _
      · positivity
      · positivity
    _ = (windowConstant*((length:ℝ)*upper^(length-1)))*centre^length := by ring
    _ ≤ epsilon*centre^length := mul_le_mul_of_nonneg_right factor_small.le (pow_nonneg centre_positive.le length)

/-- In particular powers throughout the centred window are comparable to the
actual scale rho = centre^length with universal factors one half and two. -/
theorem centered_window_power_comparable {centre windowConstant : ℝ}
    (centre_positive : 0 < centre) (centre_less_one : centre < 1)
    (window_nonnegative : 0 ≤ windowConstant) :
    ∀ᶠ length : ℕ in atTop, ∀ ratio : ℝ,
      |ratio-centre| ≤ windowConstant*centre^length →
      (1/2)*centre^length ≤ ratio^length ∧ ratio^length ≤ 2*centre^length := by
  filter_upwards [centered_window_power_relative_error centre_positive centre_less_one window_nonnegative
    (by norm_num : (0:ℝ)<1/2)] with length error_bound
  intro ratio ratio_window
  have error := abs_le.mp (error_bound ratio ratio_window)
  have positive_power := pow_pos centre_positive length
  constructor <;> linarith [error.1, error.2]

end LambdaCantor.AE


