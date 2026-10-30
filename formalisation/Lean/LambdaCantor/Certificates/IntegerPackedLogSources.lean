import LambdaCantor.Certificates.IntegerPackedLog00
import LambdaCantor.Certificates.IntegerPackedLog01
import LambdaCantor.Certificates.IntegerPackedLog02
import LambdaCantor.Certificates.IntegerPackedLog03
import LambdaCantor.Certificates.IntegerPackedLog04
import LambdaCantor.Certificates.IntegerPackedLog05
import LambdaCantor.Certificates.IntegerPackedLog06
import LambdaCantor.Certificates.IntegerPackedLog07

namespace LambdaCantor.Integer

theorem integer_log_source_301_531440 (n : ℕ) (lower : 301 ≤ n) (upper : n ≤ 531440) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      ∃ exponent, source.LogChecked n exponent := by
  by_cases h0 : n ≤ 10000
  · exact packedLogTable00_sources n lower h0
  by_cases h1 : n ≤ 50000
  · exact packedLogTable01_sources n (by omega) h1
  by_cases h2 : n ≤ 140000
  · exact packedLogTable02_sources n (by omega) h2
  by_cases h3 : n ≤ 177146
  · exact packedLogTable03_sources n (by omega) h3
  by_cases h4 : n ≤ 267146
  · exact packedLogTable04_sources n (by omega) h4
  by_cases h5 : n ≤ 357146
  · exact packedLogTable05_sources n (by omega) h5
  by_cases h6 : n ≤ 447146
  · exact packedLogTable06_sources n (by omega) h6
  · exact packedLogTable07_sources n (by omega) upper

/-- Actual real corner signs and the full logarithmic derivative-ratio band.
The finite computation is discharged by the eight explicit compiled tables;
the passage from arithmetic to real logarithms is the generic soundness proof. -/
theorem integer_real_log_source_301_531440 (n : ℕ) (lower : 301 ≤ n) (upper : n ≤ 531440) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p) -
        Real.log ((source.Q+1)/3^source.q) - Real.log n +
        (source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p) -
        Real.log ((source.Q : ℝ)/3^source.q) - Real.log n +
        (source.d : ℝ)*Real.log 3 ∧
      ((logSourceBand source.band).1 : ℝ)/(logSourceBand source.band).2.1 <
        (n : ℝ)*source.Q/(source.P+1) ∧
      (n : ℝ)*(source.Q+1)/source.P <
        ((logSourceBand source.band).2.2.1 : ℝ)/(logSourceBand source.band).2.2.2 := by
  obtain ⟨source,geometry,exponent,checked⟩ := integer_log_source_301_531440 n lower upper
  exact ⟨source,geometry,checked.real_log_corners.1,checked.real_log_corners.2,
    geometry.full_ratio_bounds.1,geometry.full_ratio_bounds.2⟩

end LambdaCantor.Integer
