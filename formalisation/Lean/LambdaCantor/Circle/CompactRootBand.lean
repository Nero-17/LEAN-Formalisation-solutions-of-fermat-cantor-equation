import LambdaCantor.Circle.RootMap
import Mathlib.Topology.Order.Compact

noncomputable section
namespace LambdaCantor.Circle

theorem circleAddressRoot_distance (depth : ℕ) (large : 2 ≤ depth) (digits : ℕ → Bool × Bool) :
    circleAddressRoot depth large digits < onset + 2 * (7 / 25 : ℝ) ^ (2 * depth + 1) := by
  have specification := circleAddressRoot_spec depth large digits
  have positive := lt_trans onset_pos specification.1.1
  have less_one : circleAddressRoot depth large digits < 1 := lt_trans specification.1.2 (by norm_num)
  have first_bounds := cantorSet_subset_unitInterval positive.le less_one
    (Set.mem_range_self (fun index => (digits index).1))
  have second_bounds := cantorSet_subset_unitInterval positive.le less_one
    (Set.mem_range_self (fun index => (digits index).2))
  apply circle_root_distance depth (fun ratio => address ratio (fun index => (digits index).1))
    (fun ratio => address ratio (fun index => (digits index).2)) specification.1.1 specification.1.2.le
    first_bounds.1 first_bounds.2 second_bounds.1 second_bounds.2
  rw [← expandedCircleResidual_eq]
  exact specification.2

/-- For each fixed cylinder depth, all address roots lie in one closed band
strictly between onset and its explicit exponentially close upper bound. -/
theorem circle_roots_compact_band (depth : ℕ) (large : 2 ≤ depth) :
    ∃ lower upper : ℝ, onset < lower ∧ lower ≤ upper ∧
      upper < onset + 2 * (7 / 25 : ℝ) ^ (2 * depth + 1) ∧ upper < 7 / 25 ∧
      ∀ digits : ℕ → Bool × Bool, circleAddressRoot depth large digits ∈ Set.Icc lower upper := by
  have compact_roots := isCompact_circleAddressRoot_range depth large
  have nonempty_roots : (Set.range (circleAddressRoot depth large)).Nonempty :=
    ⟨_, Set.mem_range_self (fun _ => (false, false))⟩
  obtain ⟨lower, lower_least⟩ := compact_roots.exists_isLeast nonempty_roots
  obtain ⟨upper, upper_greatest⟩ := compact_roots.exists_isGreatest nonempty_roots
  obtain ⟨lowerDigits, lower_eq⟩ := lower_least.1
  obtain ⟨upperDigits, upper_eq⟩ := upper_greatest.1
  refine ⟨lower, upper, ?_, lower_least.2 upper_greatest.1, ?_, ?_, ?_⟩
  · rw [← lower_eq]
    exact (circleAddressRoot_spec depth large lowerDigits).1.1
  · rw [← upper_eq]
    exact circleAddressRoot_distance depth large upperDigits
  · rw [← upper_eq]
    exact (circleAddressRoot_spec depth large upperDigits).1.2
  · intro digits
    exact ⟨lower_least.2 (Set.mem_range_self digits), upper_greatest.2 (Set.mem_range_self digits)⟩

end LambdaCantor.Circle
