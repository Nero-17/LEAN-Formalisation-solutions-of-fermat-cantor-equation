import LambdaCantor.Integer.SmallIntegerPositiveDimension
import LambdaCantor.Integer.IntegerPositiveDimension
import LambdaCantor.Integer.CubicPositiveDimension
import LambdaCantor.Integer.ExceptionalDimensions
import LambdaCantor.Classical.PositiveDimension

namespace LambdaCantor.Integer

/-- Full integer-powers theorem from the frozen manuscript. The four explicit
finite phase-cover acceptance premises are retained until their complete data
are checked; no internal certificate is replaced by an axiom. The cases n=2,
n=3 and the nine exceptional exponents use their independent actual-fibre
positive-dimension theorems. -/
theorem integer_powers_positive_dimension
    (finite12 : FiniteCoverageCertified 12) (finite13 : FiniteCoverageCertified 13)
    (finite14 : FiniteCoverageCertified 14) (tail : TailCoverageCertified)
    (n : ℕ) (exponent : 2 ≤ n) :
    0 < dimH (intersection (n : ℝ) (1/3)) := by
  by_cases quadratic : n = 2
  · subst n
    exact Classical.classical_circle_positive_dimension
  by_cases cubic : n = 3
  · subst n
    exact cubic_intersection_positive_dimension
  by_cases large : 301 ≤ n
  · exact integer_positive_dimension_ge_301 finite12 finite13 finite14 tail n large
  by_cases exceptional : n ∈ ([9,10,23,25,28,31,32,78,82] : List ℕ)
  · apply Exceptional.nine_exceptional_exponents_positive_dimension n
    simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using exceptional
  · exact small_integer_positive_dimension n (by omega) (by omega) exceptional

#print axioms integer_powers_positive_dimension

end LambdaCantor.Integer
