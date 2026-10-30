import LambdaCantor.Certificates.IntegerExceptionalDimension9
import LambdaCantor.Certificates.IntegerExceptionalDimension10
import LambdaCantor.Certificates.IntegerExceptionalDimension23
import LambdaCantor.Certificates.IntegerExceptionalDimension25
import LambdaCantor.Certificates.IntegerExceptionalDimension28
import LambdaCantor.Certificates.IntegerExceptionalDimension31
import LambdaCantor.Certificates.IntegerExceptionalDimension32
import LambdaCantor.Certificates.IntegerExceptionalDimension78
import LambdaCantor.Certificates.IntegerExceptionalDimension82

namespace LambdaCantor.Integer.Exceptional

/-- The nine exceptional exponents in the frozen manuscript, discharged by
their own actual finite-return certificates and nonlinear dimension transfer. -/
theorem nine_exceptional_exponents_positive_dimension (exponent : ℕ)
    (listed : exponent = 9 ∨ exponent = 10 ∨ exponent = 23 ∨ exponent = 25 ∨
      exponent = 28 ∨ exponent = 31 ∨ exponent = 32 ∨ exponent = 78 ∨ exponent = 82) :
    0 < dimH (intersection (exponent : ℝ) (1/3)) := by
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact N9.positive_dimension
  · exact N10.positive_dimension
  · exact N23.positive_dimension
  · exact N25.positive_dimension
  · exact N28.positive_dimension
  · exact N31.positive_dimension
  · exact N32.positive_dimension
  · exact N78.positive_dimension
  · exact N82.positive_dimension

#print axioms nine_exceptional_exponents_positive_dimension
end LambdaCantor.Integer.Exceptional
