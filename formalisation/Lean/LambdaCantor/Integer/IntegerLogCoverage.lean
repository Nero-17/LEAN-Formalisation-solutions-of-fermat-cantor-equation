import LambdaCantor.Integer.FiniteCoverageCertificate
import LambdaCantor.Integer.TailIntegerTransfer
import LambdaCantor.Certificates.IntegerPackedLogSources

namespace LambdaCantor.Integer

/-- The entire exponent range above the exceptional small cases. The only
remaining inputs are acceptance of the three finite phase covers and the tail
cover; all source geometry and logarithmic inequalities are conclusions. -/
theorem integer_log_source_ge_301
    (finite12 : FiniteCoverageCertified 12) (finite13 : FiniteCoverageCertified 13)
    (finite14 : FiniteCoverageCertified 14) (tail : TailCoverageCertified)
    (n : ℕ) (large : 301 ≤ n) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 := by
  by_cases bounded : n ≤ 531440
  · obtain ⟨source,geometry,exponent,checked⟩ := integer_log_source_301_531440 n large bounded
    exact ⟨source,geometry,checked.real_log_corners⟩
  by_cases below13 : n ≤ 3^13
  · exact integer_finite_log_source 12 finite12 n (by omega) (by norm_num; omega) below13
  by_cases below14 : n ≤ 3^14
  · exact integer_finite_log_source 13 finite13 n (by omega) (by omega) below14
  by_cases below15 : n ≤ 3^15
  · exact integer_finite_log_source 14 finite14 n (by omega) (by omega) below15
  · exact integer_tail_log_source tail n (by omega)

end LambdaCantor.Integer
