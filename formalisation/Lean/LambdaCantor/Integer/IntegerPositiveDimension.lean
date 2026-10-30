import LambdaCantor.Integer.IntegerLogCoverage
import LambdaCantor.Integer.LogSourcePositiveDimension

namespace LambdaCantor.Integer

theorem integer_positive_dimension_ge_301
    (finite12 : FiniteCoverageCertified 12) (finite13 : FiniteCoverageCertified 13)
    (finite14 : FiniteCoverageCertified 14) (tail : TailCoverageCertified)
    (n : ℕ) (large : 301 ≤ n) :
    0 < dimH (intersection (n : ℝ) (1/3)) := by
  obtain ⟨source,geometry,lower,upper⟩ := integer_log_source_ge_301 finite12 finite13 finite14 tail n large
  exact geometry_log_source_positive_dimension n source geometry ⟨lower,upper⟩

#print axioms integer_positive_dimension_ge_301

end LambdaCantor.Integer
