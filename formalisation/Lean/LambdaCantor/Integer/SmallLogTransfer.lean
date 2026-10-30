import LambdaCantor.Integer.LogCertificateTransfer
import LambdaCantor.Integer.LogSourceBounds

namespace LambdaCantor.Integer

theorem LogSourceData.Valid.geometry {n : ℕ} {source : LogSourceData}
    (valid : source.Valid n) : source.GeometryChecked n := by
  obtain ⟨hn,hP,hQ,prefixP,prefixQ,boundP,boundQ,_,_,lower,upper⟩ := valid
  exact ⟨hn,hP,hQ,prefixP,prefixQ,boundP,boundQ,lower,upper⟩

theorem LogSourceData.Valid.log_corners {n : ℕ} {source : LogSourceData}
    (valid : source.Valid n) :
    (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
      Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
    0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
      Real.log n+(source.d : ℝ)*Real.log 3 := by
  have corners := LogSourceData.real_corners valid
  obtain ⟨hn,hP,hQ,_,_,_,_,_,_,_,_⟩ := valid
  have nPositive : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have pPositive : (0 : ℝ) < source.P := by exact_mod_cast hP
  have qPositive : (0 : ℝ) < source.Q := by exact_mod_cast hQ
  have first := Real.log_lt_log (by positivity) corners.1
  have second := Real.log_lt_log (by positivity) corners.2
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,
    Real.log_mul (ne_of_gt nPositive) (by positivity)] at first
  rw [Real.log_mul (ne_of_gt nPositive) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow] at second
  exact ⟨by linarith,by linarith⟩

theorem valid_log_source_normalized_transfer (n : ℕ) (source : LogSourceData)
    (valid : source.Valid n) :
    ∃ k : ℕ, ∃ point ∈ Classical.cantorLevel
      (nearAxisLog n source.d source.p source.q source.P source.Q
        ((1/3 : ℝ)^(n*k+source.d))) 0,
      (GoodSlope (nearAxisHorizontal n source.P point.1/
        nearAxisVertical n source.q source.Q ((1/3 : ℝ)^(n*k+source.d)) point.2) ∧
        ∀ rational : ℚ, nearAxisHorizontal n source.P point.1/
          nearAxisVertical n source.q source.Q ((1/3 : ℝ)^(n*k+source.d)) point.2 ≠ (rational : ℝ)) ∨
      (GoodSlope (nearAxisVertical n source.q source.Q ((1/3 : ℝ)^(n*k+source.d)) point.2/
        nearAxisHorizontal n source.P point.1) ∧
        ∀ rational : ℚ, nearAxisVertical n source.q source.Q ((1/3 : ℝ)^(n*k+source.d)) point.2/
          nearAxisHorizontal n source.P point.1 ≠ (rational : ℝ)) :=
  geometry_log_source_normalized_transfer n source valid.geometry valid.log_corners

end LambdaCantor.Integer
