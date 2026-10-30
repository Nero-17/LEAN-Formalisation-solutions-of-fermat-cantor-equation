import LambdaCantor.AE.CenteredWindowPower
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open Filter Set
open scoped Topology

namespace LambdaCantor.AE

/-- Exponentially close freezing points have uniformly comparable prefix
powers. The hypothesis b squared below a is the same compact-band condition
used by the normalized Newton transport cost. -/
theorem freezing_power_relative_bound {lower upper displacementConstant : ℝ}
    (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (square_less : upper*upper < lower) (displacement_nonnegative : 0 ≤ displacementConstant) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ (depth : ℕ) (rho first second : ℝ),
      0 ≤ rho → first ∈ Icc lower upper → second ∈ Icc lower upper →
      |first-second| ≤ displacementConstant*rho*upper^depth →
      |first^depth-second^depth| ≤ constant*rho*first^depth := by
  have quotient_nonnegative : 0 ≤ upper*upper/lower := by positivity
  have quotient_less : upper*upper/lower < 1 := (div_lt_one lower_positive).mpr square_less
  obtain ⟨bound, bound_range⟩ :=
    (tendsto_self_mul_const_pow_of_lt_one quotient_nonnegative quotient_less).bddAbove_range
  have bound_nonnegative : 0 ≤ bound := by
    simpa using bound_range (show (0 : ℝ) ∈ range (fun depth : ℕ =>
      (depth : ℝ)*(upper*upper/lower)^depth) from ⟨0, by simp⟩)
  refine ⟨displacementConstant/upper*(bound+1)+1, by positivity, ?_⟩
  intro depth rho first second rho_nonnegative first_mem second_mem displacement
  by_cases depth_zero : depth = 0
  · subst depth
    simp only [pow_zero, sub_self, abs_zero]
    positivity
  have maximum : max |first| |second| ≤ upper := by
    rw [abs_of_pos (lower_positive.trans_le first_mem.1), abs_of_pos (lower_positive.trans_le second_mem.1)]
    exact max_le first_mem.2 second_mem.2
  have derivative_bound := abs_pow_sub_pow_le first second depth
  have power_bound : max |first| |second|^(depth-1) ≤ upper^(depth-1) :=
    pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg first)) maximum _
  have absolute_bound : |first^depth-second^depth| ≤
      displacementConstant*rho*upper^depth*(depth : ℝ)*upper^(depth-1) := by
    apply derivative_bound.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_right displacement (Nat.cast_nonneg depth))
      power_bound (by positivity) (by positivity)
  have previous_power : upper^(depth-1) = upper^depth/upper := by
    have identity : upper^(depth-1)*upper = upper^depth := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr depth_zero)]
    exact (eq_div_iff upper_positive.ne').mpr identity
  have factorization : displacementConstant*rho*upper^depth*(depth : ℝ)*upper^(depth-1) =
      (displacementConstant/upper*((depth : ℝ)*(upper*upper/lower)^depth))*rho*lower^depth := by
    rw [previous_power, div_pow, mul_pow]
    field_simp [upper_positive.ne', lower_positive.ne']
    <;> ring
  have sequence_bound : (depth : ℝ)*(upper*upper/lower)^depth ≤ bound :=
    bound_range ⟨depth, rfl⟩
  have coefficient_bound : displacementConstant/upper*((depth : ℝ)*(upper*upper/lower)^depth) ≤
      displacementConstant/upper*(bound+1)+1 := by
    have multiplied := mul_le_mul_of_nonneg_left sequence_bound
      (div_nonneg displacement_nonnegative upper_positive.le)
    nlinarith [div_nonneg displacement_nonnegative upper_positive.le]
  calc
    _ ≤ displacementConstant*rho*upper^depth*(depth : ℝ)*upper^(depth-1) := absolute_bound
    _ = _ := factorization
    _ ≤ (displacementConstant/upper*(bound+1)+1)*rho*first^depth := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right coefficient_bound rho_nonnegative
      · exact pow_le_pow_left₀ lower_positive.le first_mem.1 depth
      · positivity
      · positivity

theorem freezing_powers_eventually_comparable {lower upper center displacementConstant : ℝ}
    (lower_positive : 0 < lower) (upper_positive : 0 < upper)
    (square_less : upper*upper < lower) (center_nonnegative : 0 ≤ center) (center_less_one : center < 1)
    (displacement_nonnegative : 0 ≤ displacementConstant) :
    ∀ᶠ length : ℕ in atTop, ∀ (depth : ℕ) (first second : ℝ),
      first ∈ Icc lower upper → second ∈ Icc lower upper →
      |first-second| ≤ displacementConstant*center^length*upper^depth →
      (1/2)*first^depth ≤ second^depth ∧ second^depth ≤ 2*first^depth := by
  obtain ⟨constant, constant_positive, relative⟩ := freezing_power_relative_bound
    lower_positive upper_positive square_less displacement_nonnegative
  have limit : Tendsto (fun length : ℕ => constant*center^length) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one center_nonnegative center_less_one).const_mul constant
  filter_upwards [limit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))]
    with length small
  intro depth first second first_mem second_mem displacement
  have error := (relative depth (center^length) first second (pow_nonneg center_nonnegative _)
    first_mem second_mem displacement).trans
      (mul_le_mul_of_nonneg_right small.le (pow_nonneg (lower_positive.le.trans first_mem.1) depth))
  have absolute := abs_le.mp error
  have power_nonnegative := pow_nonneg (lower_positive.le.trans first_mem.1) depth
  constructor <;> linarith [absolute.1, absolute.2]

end LambdaCantor.AE
