import LambdaCantor.Classical.FirstSubdivision

noncomputable section
namespace LambdaCantor.PaperExamples

/-- The exact polynomial displayed in manuscript Example 2.7. -/
def subdivisionResidual (firstDigit secondDigit firstTail secondTail : ℝ) : ℝ :=
  (19008 + firstDigit + firstTail) ^ 2 +
    9 * (1698 + secondDigit + secondTail) ^ 2 - 3 ^ 18

theorem subdivisionResidual_identity (firstDigit secondDigit firstTail secondTail : ℝ) :
    subdivisionResidual firstDigit secondDigit firstTail secondTail =
      9 * (Classical.cylinderPolynomial ((firstDigit + firstTail) / 3)
        ((secondDigit + secondTail) / 3) - 3 ^ 16) := by
  unfold subdivisionResidual Classical.cylinderPolynomial
  ring

theorem first_subdivision_corner_table :
    subdivisionResidual 0 0 0 0 = -167589 ∧
    subdivisionResidual 0 0 1 1 = -98999 ∧
    subdivisionResidual 0 2 0 0 = -106425 ∧
    subdivisionResidual 0 2 1 1 = -37799 ∧
    subdivisionResidual 2 0 0 0 = -91553 ∧
    subdivisionResidual 2 0 1 1 = -22959 ∧
    subdivisionResidual 2 2 0 0 = -30389 ∧
    subdivisionResidual 2 2 1 1 = 38241 := by
  norm_num [subdivisionResidual]

#print axioms subdivisionResidual_identity
#print axioms first_subdivision_corner_table
#print axioms LambdaCantor.Classical.source_first_digits_true

end LambdaCantor.PaperExamples
