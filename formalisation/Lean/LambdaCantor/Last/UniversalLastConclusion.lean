import LambdaCantor.Last.AnalyticIrrational
import LambdaCantor.Last.AnalyticExceptionsHalf
import LambdaCantor.Last.RationalLastConclusion
import Mathlib.Data.Rat.Cast.Order
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last

/-- The actual universal strict last-transition bound, with the reduced
rational representation derived internally from the real exponent. -/
theorem universal_lastTransition_lt_critical {exponent : ℝ} (hexponent : 1 < exponent) :
    lastTransition exponent < (Real.sqrt 3 - 1) / 2 := by
  by_cases hirrational : Irrational exponent
  · exact analytic_irrational_last_strict_upper hirrational hexponent
  obtain ⟨rational, hrational⟩ := exists_rat_of_not_irrational hirrational
  have hrational_positive : (0 : ℚ) < rational := by
    have hreal_positive : (0 : ℝ) < rational := by rw [← hrational]; linarith
    exact_mod_cast hreal_positive
  have hnumerator_positive : 0 < rational.num := Rat.num_pos.mpr hrational_positive
  have hnumerator_cast : ((rational.num.natAbs : ℕ) : ℝ) = (rational.num : ℝ) := by
    have hinteger_cast : (rational.num.natAbs : ℤ) = rational.num := by
      rw [Int.natCast_natAbs, abs_of_nonneg hnumerator_positive.le]
    simpa only [Int.cast_natCast] using
      congrArg (fun integer : ℤ => (integer : ℝ)) hinteger_cast
  have hrepresentation : exponent = (rational.num.natAbs : ℝ) / rational.den := by
    rw [hrational, Rat.cast_def, hnumerator_cast]
  have hdenominator_positive : 0 < rational.den := rational.pos
  have hdenominator_real : (0 : ℝ) < rational.den := by exact_mod_cast hdenominator_positive
  have hordered : rational.den < rational.num.natAbs := by
    have hcleared := (one_lt_div hdenominator_real).mp (hrepresentation ▸ hexponent)
    exact_mod_cast hcleared
  by_cases hlarge : 4 ≤ rational.num.natAbs
  · rw [hrepresentation]
    exact rational_lastTransition_lt_critical hlarge hdenominator_positive rational.reduced hordered
  have hsmall :
      (rational.num.natAbs = 2 ∧ rational.den = 1) ∨
      (rational.num.natAbs = 3 ∧ rational.den = 1) ∨
      (rational.num.natAbs = 3 ∧ rational.den = 2) := by omega
  rcases hsmall with ⟨hnumerator, hdenominator⟩ | ⟨hnumerator, hdenominator⟩ | ⟨hnumerator, hdenominator⟩
  · simpa [hrepresentation, hnumerator, hdenominator] using analytic_quadratic_last_strict_upper
  · simpa [hrepresentation, hnumerator, hdenominator] using analytic_cubic_last_strict_upper
  · simpa [hrepresentation, hnumerator, hdenominator] using analytic_three_halves_last_strict_upper

end LambdaCantor.Last
