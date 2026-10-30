import LambdaCantor.Integer.SmallLogTransfer
import LambdaCantor.Integer.LogSourcePositiveDimension
import LambdaCantor.Certificates.IntegerLogSources

namespace LambdaCantor.Integer

/-- All 288 repaired nonexceptional small certificates imply positive dimension
of their actual middle-thirds Fermat intersections. -/
theorem small_integer_positive_dimension (n : ℕ) (lower : 4 ≤ n) (upper : n ≤ 300)
    (nonexceptional : n ∉ ([9,10,23,25,28,31,32,78,82] : List ℕ)) :
    0 < dimH (intersection (n : ℝ) (1/3)) := by
  obtain ⟨source,valid⟩ := finite_refined_log_sources n lower upper nonexceptional
  exact geometry_log_source_positive_dimension n source valid.geometry valid.log_corners

#print axioms small_integer_positive_dimension

end LambdaCantor.Integer
