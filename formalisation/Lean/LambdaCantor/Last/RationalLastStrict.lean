import LambdaCantor.Last.RationalLastPerfectPersistence
import LambdaCantor.Last.RationalLastActualIsolationFermat
import LambdaCantor.Last.RationalLastActualIsolationAbove
import LambdaCantor.Last.Transitions
import LambdaCantor.Half

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem rational_positive_dimension_at_or_above_critical_of_infinite
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : denominator < numerator) {ratio : ℝ}
    (above_critical : (Real.sqrt 3-1)/2 ≤ ratio) (less_half : ratio < 1/2)
    (infinite : (intersection ((numerator : ℝ)/denominator) ratio).Infinite) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) ratio) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < ratio := by nlinarith
  have less_one : ratio < 1 := by linarith
  have rational_gt_one : 1 < (numerator : ℝ)/denominator :=
    (one_lt_div (show (0 : ℝ) < denominator by exact_mod_cast denominator_positive)).mpr
      (by exact_mod_cast exponent_gt_one)
  have finite_isolated : (isolatedPoints (intersection ((numerator : ℝ)/denominator) ratio)).Finite := by
    rcases lt_or_eq_of_le above_critical with above | critical
    · exact finite_isolated_actual_rational_intersection_above_critical numerator_large
        denominator_positive coprime exponent_gt_one above less_half
    · exact finite_isolated_actual_rational_intersection_at_critical numerator_large
        denominator_positive coprime exponent_gt_one critical.symm
  exact actual_fermat_positive_dimension_of_infinite_of_finite_isolated rational_gt_one above_critical less_half
    (isCompact_intersection (by linarith) positive.le less_one) infinite finite_isolated

theorem rational_positive_dimension_near_critical_of_infinite
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : denominator < numerator)
    (infinite : (intersection ((numerator : ℝ)/denominator) ((Real.sqrt 3-1)/2)).Infinite) :
    ∀ᶠ ratio in 𝓝 ((Real.sqrt 3-1)/2),
      0 < dimH (intersection ((numerator : ℝ)/denominator) ratio) := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have positive : 0 < (Real.sqrt 3-1)/2 := by nlinarith
  have less_half : (Real.sqrt 3-1)/2 < (1/2 : ℝ) := by nlinarith
  have rational_gt_one : 1 < (numerator : ℝ)/denominator :=
    (one_lt_div (show (0 : ℝ) < denominator by exact_mod_cast denominator_positive)).mpr
      (by exact_mod_cast exponent_gt_one)
  exact actual_fermat_positive_dimension_persist_of_infinite_of_finite_isolated rational_gt_one le_rfl less_half
    (isCompact_intersection (by linarith) positive.le (by linarith)) infinite
    (finite_isolated_actual_rational_intersection_at_critical numerator_large denominator_positive coprime
      exponent_gt_one rfl)

/-- The remaining geometric input is stated exactly: actual infinitude of
the rational intersection throughout the upper critical interval. Once the
coarse endpoint theorem supplies it, this theorem leaves no isolated-point,
perfect-set, perturbation, half-endpoint, or supremum premise. -/
theorem rational_lastTransition_lt_critical_of_infinite_intersections
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : denominator < numerator)
    (infinite : ∀ ratio : ℝ, (Real.sqrt 3-1)/2 ≤ ratio → ratio < 1/2 →
      (intersection ((numerator : ℝ)/denominator) ratio).Infinite) :
    lastTransition ((numerator : ℝ)/denominator) < (Real.sqrt 3-1)/2 := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have critical_positive : 0 < (Real.sqrt 3-1)/2 := by nlinarith
  have critical_less_half : (Real.sqrt 3-1)/2 < (1/2 : ℝ) := by nlinarith
  have rational_gt_one : 1 < (numerator : ℝ)/denominator :=
    (one_lt_div (show (0 : ℝ) < denominator by exact_mod_cast denominator_positive)).mpr
      (by exact_mod_cast exponent_gt_one)
  have near := rational_positive_dimension_near_critical_of_infinite numerator_large denominator_positive coprime
    exponent_gt_one (infinite _ le_rfl critical_less_half)
  obtain ⟨radius, radius_positive, near_positive⟩ := Metric.mem_nhds_iff.mp near
  have bound_less : max 0 ((Real.sqrt 3-1)/2-radius/2) < (Real.sqrt 3-1)/2 :=
    max_lt critical_positive (by linarith)
  apply (lastTransition_le_of_nonnegative_bound (le_max_left _ _) ?_).trans_lt bound_less
  intro ratio ratio_mem above_bound
  rcases lt_or_eq_of_le ratio_mem.2 with below_half | at_half
  · by_cases above_critical : (Real.sqrt 3-1)/2 ≤ ratio
    · exact rational_positive_dimension_at_or_above_critical_of_infinite numerator_large denominator_positive
        coprime exponent_gt_one above_critical below_half (infinite ratio above_critical below_half)
    · apply near_positive
      apply Metric.mem_ball.mpr
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      have lower := (le_max_right 0 ((Real.sqrt 3-1)/2-radius/2)).trans_lt above_bound
      linarith
  · rw [at_half]
    exact positive_dimH_intersection_half (by linarith)

end LambdaCantor.Last
