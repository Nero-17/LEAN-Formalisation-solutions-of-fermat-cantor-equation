import LambdaCantor.Integer.NearAxisReciprocalDimension
import LambdaCantor.Integer.LogCertificateTransfer

namespace LambdaCantor.Integer

theorem geometry_log_source_positive_dimension (n : ℕ) (source : LogSourceData)
    (geometry : source.GeometryChecked n)
    (cornerSigns :
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3) :
    0 < dimH (intersection (n : ℝ) (1/3)) := by
  have ratio := geometry.full_ratio_bounds
  obtain ⟨positiveN,positiveP,positiveQ,prefixP,prefixQ,boundP,boundQ,_,_⟩ := geometry
  have positivePReal : (0 : ℝ) < source.P := by exact_mod_cast positiveP
  have positiveQReal : (0 : ℝ) < source.Q := by exact_mod_cast positiveQ
  have lowerRatio : (((logSourceBand source.band).1 : ℝ)/(logSourceBand source.band).2.1)/source.Q <
      (n : ℝ)/(source.P+1) := by
    apply (div_lt_iff₀ positiveQReal).2
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using ratio.1
  have upperRatio : (n : ℝ)/source.P <
      (((logSourceBand source.band).2.2.1 : ℝ)/(logSourceBand source.band).2.2.2)/(source.Q+1) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < source.Q+1)).2
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using ratio.2
  have lowerCorner : nearAxisLog n source.d source.p source.q source.P source.Q 0 0 0 < 0 := by
    rw [nearAxisLog_zero n source.d source.p source.q source.P source.Q 0 0
      (by omega) (by linarith)]
    simp only [add_zero,sub_zero]
    linarith [cornerSigns.1]
  have upperCorner : 0 < nearAxisLog n source.d source.p source.q source.P source.Q 0 1 1 := by
    rw [nearAxisLog_zero n source.d source.p source.q source.P source.Q 1 1
      (by omega) (by linarith)]
    simp only [add_sub_cancel_right]
    linarith [cornerSigns.2]
  by_cases direct : source.band.val < 5
  · obtain ⟨lowerBand,upperBand,positiveB,good⟩ := direct_log_band_properties source.band direct
    exact strict_log_source_positive_dimension n source.d source.p source.q source.P source.Q _ _
      positiveN positiveP positiveQ prefixP prefixQ boundQ lowerBand upperBand positiveB good
      lowerRatio upperRatio lowerCorner upperCorner
  · obtain ⟨lowerBand,upperBand,positiveB,good⟩ := reciprocal_log_band_properties source.band (by omega)
    exact reciprocal_strict_log_source_positive_dimension n source.d source.p source.q source.P source.Q _ _
      positiveN positiveP positiveQ prefixP prefixQ boundQ lowerBand upperBand positiveB good
      lowerRatio upperRatio lowerCorner upperCorner

end LambdaCantor.Integer
