import LambdaCantor.First.RootsResidualEstimates
import Mathlib.Topology.Order.Compact

noncomputable section
namespace LambdaCantor.First.Roots

theorem rpow_lipschitz_positive_band {lowerCoordinate exponent left right : ℝ}
    (lower_positive : 0 < lowerCoordinate)
    (left_mem : left ∈ Set.Icc lowerCoordinate 1) (right_mem : right ∈ Set.Icc lowerCoordinate 1) :
    |left ^ exponent - right ^ exponent| ≤
      (|exponent| * max 1 (lowerCoordinate ^ (exponent - 1))) * |left - right| := by
  have derivative (point : ℝ) (point_mem : point ∈ Set.Icc lowerCoordinate 1) :=
    Real.hasDerivAt_rpow_const (p := exponent) (Or.inl (ne_of_gt (lower_positive.trans_le point_mem.1)))
  have derivative_bound : ∀ point ∈ Set.Icc lowerCoordinate 1,
      ‖exponent * point ^ (exponent - 1)‖ ≤ |exponent| * max 1 (lowerCoordinate ^ (exponent - 1)) := by
    intro point point_mem
    have point_positive := lower_positive.trans_le point_mem.1
    have power_bound : point ^ (exponent - 1) ≤ max 1 (lowerCoordinate ^ (exponent - 1)) := by
      by_cases nonnegative : 0 ≤ exponent - 1
      · exact (Real.rpow_le_one point_positive.le point_mem.2 nonnegative).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_nonpos lower_positive point_mem.1 (lt_of_not_ge nonnegative).le).trans
          (le_max_right _ _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg point_positive.le _)]
    exact mul_le_mul_of_nonneg_left power_bound (abs_nonneg _)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc lowerCoordinate 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun point point_mem => (derivative point point_mem).hasDerivWithinAt)
      derivative_bound right_mem left_mem

/-- The minimum fixed cylinder endpoint already bounds every unrestricted
tail. Thus positivity on the band supplies one common positive coordinate
lower bound without choosing any tail-dependent constants. -/
theorem rootFibreData_uniform_positive_coordinates {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ lowerCoordinate : ℝ, 0 < lowerCoordinate ∧
      ∀ (digits : ℕ → Bool × Bool) (ratio : ℝ), ratio ∈ Set.Icc data.lower data.upper →
        lowerCoordinate ≤ cylinderCoordinate data.leftWord data.leftLength (fun index => (digits index).1) ratio ∧
        lowerCoordinate ≤ cylinderCoordinate data.rightWord data.rightLength (fun index => (digits index).2) ratio := by
  have endpoint_continuous : Continuous (fun ratio : ℝ =>
      min (prefixValue ratio data.leftWord data.leftLength)
        (prefixValue ratio data.rightWord data.rightLength)) := by
    unfold prefixValue
    fun_prop
  obtain ⟨minimumParameter, minimum_mem, minimum_property⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr data.ordered) endpoint_continuous.continuousOn
  have zero_address (ratio : ℝ) : address ratio (fun _ => false) = 0 := by
    simp [address]
  have left_positive := data.left_positive (fun _ => (false, false)) minimumParameter minimum_mem
  have right_positive := data.right_positive (fun _ => (false, false)) minimumParameter minimum_mem
  simp only [cylinderCoordinate, zero_address, mul_zero, add_zero] at left_positive right_positive
  refine ⟨min (prefixValue minimumParameter data.leftWord data.leftLength)
      (prefixValue minimumParameter data.rightWord data.rightLength),
    lt_min left_positive right_positive, ?_⟩
  intro digits ratio in_band
  have ratio_nonnegative : 0 ≤ ratio := by linarith [data.lower_gt_quarter, in_band.1]
  have ratio_lt_one : ratio < 1 := by linarith [data.upper_lt_half, in_band.2]
  have lower_bound := minimum_property in_band
  constructor
  · apply (lower_bound.trans (min_le_left _ _)).trans
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg ratio_nonnegative _)
      (address_nonnegative ratio_nonnegative ratio_lt_one _))
  · apply (lower_bound.trans (min_le_right _ _)).trans
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg ratio_nonnegative _)
      (address_nonnegative ratio_nonnegative ratio_lt_one _))

end LambdaCantor.First.Roots
