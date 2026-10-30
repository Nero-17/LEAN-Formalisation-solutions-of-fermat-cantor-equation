import LambdaCantor.Circle.ZeroDimensionIntervals
import LambdaCantor.Last.Transitions

noncomputable section
namespace LambdaCantor.Circle

/-- The strict last-transition bound follows from the zero windows alone. -/
theorem onset_lt_lastTransition : onset < lastTransition 2 := by
  obtain ⟨left, right, ordered, subset, zero_dimension⟩ :=
    zero_dimension_intervals_arbitrarily_close ((1 / 2 : ℝ) - onset)
      (by linarith [onset_lt_one_third])
  have midpoint_member : (left + right) / 2 ∈ Set.Ioo left right := by constructor <;> linarith
  have midpoint_bounds := subset midpoint_member
  have admissible : (left + right) / 2 ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    ⟨onset_pos.trans midpoint_bounds.1, by linarith [midpoint_bounds.2]⟩
  exact midpoint_bounds.1.trans_le (le_lastTransition_of_zero admissible
    (zero_dimension _ midpoint_member))

end LambdaCantor.Circle
