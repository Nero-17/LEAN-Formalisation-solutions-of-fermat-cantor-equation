import LambdaCantor.First.Section3TerminalAudit

noncomputable section
namespace LambdaCantor.Manuscript

/-- The full statement of introductory Theorem 1.2 in manuscript 429d53b. -/
theorem introductory_first_transition (exponent : ℝ) (above_one : 1 < exponent) :
    1 / 4 ≤ firstTransition exponent ∧
      (Irrational exponent → firstTransition exponent = 1 / 4) := by
  exact ⟨First.first_lower above_one,
    fun irrational => First.irrational_onset irrational above_one⟩

end LambdaCantor.Manuscript

#check LambdaCantor.Manuscript.introductory_first_transition
#print axioms LambdaCantor.Manuscript.introductory_first_transition
