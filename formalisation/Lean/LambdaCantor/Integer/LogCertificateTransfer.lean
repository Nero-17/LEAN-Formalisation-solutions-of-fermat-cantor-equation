import LambdaCantor.Integer.NearAxisReciprocalSource
import LambdaCantor.Certificates.IntegerPackedLogDefinition
import Mathlib.Data.Fintype.Fin

namespace LambdaCantor.Integer

theorem direct_log_band_properties (band : Fin 10) (direct : band.val < 5) :
    1 < ((logSourceBand band).1 : ℝ)/(logSourceBand band).2.1 ∧
    ((logSourceBand band).2.2.1 : ℝ)/(logSourceBand band).2.2.2 < 3 ∧
    0 < ((logSourceBand band).2.2.1 : ℝ)/(logSourceBand band).2.2.2 ∧
    ∀ slope : ℝ, ((logSourceBand band).1 : ℝ)/(logSourceBand band).2.1 < slope →
      slope < ((logSourceBand band).2.2.1 : ℝ)/(logSourceBand band).2.2.2 → GoodSlope slope := by
  fin_cases band
  · change 1 < (89 : ℝ)/73 ∧ (171 : ℝ)/137 < 3 ∧ 0 < (171 : ℝ)/137 ∧
      ∀ slope : ℝ, (89 : ℝ)/73 < slope → slope < (171 : ℝ)/137 → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inl ⟨lower,upper⟩
  · change 1 < (101 : ℝ)/79 ∧ (183 : ℝ)/143 < 3 ∧ 0 < (183 : ℝ)/143 ∧
      ∀ slope : ℝ, (101 : ℝ)/79 < slope → slope < (183 : ℝ)/143 → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inl ⟨lower,upper⟩)
  · change 1 < (89 : ℝ)/57 ∧ (171 : ℝ)/89 < 3 ∧ 0 < (171 : ℝ)/89 ∧
      ∀ slope : ℝ, (89 : ℝ)/57 < slope → slope < (171 : ℝ)/89 → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · change 1 < (143 : ℝ)/61 ∧ (237 : ℝ)/101 < 3 ∧ 0 < (237 : ℝ)/101 ∧
      ∀ slope : ℝ, (143 : ℝ)/61 < slope → slope < (237 : ℝ)/101 → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨lower,upper⟩)))
  · change 1 < (137 : ℝ)/57 ∧ (219 : ℝ)/89 < 3 ∧ 0 < (219 : ℝ)/89 ∧
      ∀ slope : ℝ, (137 : ℝ)/57 < slope → slope < (219 : ℝ)/89 → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨lower,upper⟩)))
  · norm_num at direct
  · norm_num at direct
  · norm_num at direct
  · norm_num at direct
  · norm_num at direct

/-- Every direct-band arithmetic certificate is connected to an actual
irrational tangent, without postulating any analytic source hypotheses. -/
theorem checked_direct_log_source_transfer (n exponent : ℕ) (source : LogSourceData)
    (geometry : source.GeometryChecked n) (checked : source.LogChecked n exponent)
    (direct : source.band.val < 5) :
    ∃ point : ℝ × ℝ, point.1 ∈ _root_.cantorSet ∧ point.2 ∈ _root_.cantorSet ∧
      0 < point.1 ∧ 0 < point.2 ∧ point.1^n+point.2^n=1 ∧
      ∀ rational : ℚ, fermatTangent n point ≠ (rational : ℝ) := by
  have ratio := geometry.full_ratio_bounds
  obtain ⟨lowerBand,upperBand,positiveB,bandGood⟩ := direct_log_band_properties source.band direct
  obtain ⟨positiveN,positiveP,positiveQ,prefixP,prefixQ,boundP,boundQ,_,_⟩ := geometry
  have positivePReal : (0 : ℝ) < source.P := by exact_mod_cast positiveP
  have positiveQReal : (0 : ℝ) < source.Q := by exact_mod_cast positiveQ
  apply strict_log_source_actual_irrational_tangent n source.d source.p source.q source.P source.Q
    (((logSourceBand source.band).1 : ℝ)/(logSourceBand source.band).2.1)
    (((logSourceBand source.band).2.2.1 : ℝ)/(logSourceBand source.band).2.2.2)
    positiveN positiveP positiveQ prefixP prefixQ boundQ
    lowerBand upperBand positiveB bandGood
  · apply (div_lt_iff₀ positiveQReal).2
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using ratio.1
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < source.Q+1)).2
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using ratio.2
  · rw [nearAxisLog_zero n source.d source.p source.q source.P source.Q 0 0
      (by omega) (by linarith)]
    simp only [add_zero,sub_zero]
    linarith [checked.real_log_corners.1]
  · rw [nearAxisLog_zero n source.d source.p source.q source.P source.Q 1 1
      (by omega) (by linarith)]
    simp only [add_sub_cancel_right]
    linarith [checked.real_log_corners.2]

theorem reciprocal_log_band_properties (band : Fin 10) (reciprocal : 5 ≤ band.val) :
    1/3 < ((logSourceBand band).1 : ℝ)/(logSourceBand band).2.1 ∧
    ((logSourceBand band).2.2.1 : ℝ)/(logSourceBand band).2.2.2 < 1 ∧
    0 < ((logSourceBand band).2.2.1 : ℝ)/(logSourceBand band).2.2.2 ∧
    ∀ slope : ℝ,
      1/(((logSourceBand band).2.2.1 : ℝ)/(logSourceBand band).2.2.2) < slope →
      slope < 1/(((logSourceBand band).1 : ℝ)/(logSourceBand band).2.1) → GoodSlope slope := by
  fin_cases band
  · norm_num at reciprocal
  · norm_num at reciprocal
  · norm_num at reciprocal
  · norm_num at reciprocal
  · norm_num at reciprocal
  · change (1 : ℝ)/3 < (137 : ℝ)/171 ∧ (73 : ℝ)/89 < 1 ∧ 0 < (73 : ℝ)/89 ∧
      ∀ slope : ℝ, 1/((73 : ℝ)/89) < slope → slope < 1/((137 : ℝ)/171) → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inl ⟨lower,upper⟩
  · change (1 : ℝ)/3 < (143 : ℝ)/183 ∧ (79 : ℝ)/101 < 1 ∧ 0 < (79 : ℝ)/101 ∧
      ∀ slope : ℝ, 1/((79 : ℝ)/101) < slope → slope < 1/((143 : ℝ)/183) → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inl ⟨lower,upper⟩)
  · change (1 : ℝ)/3 < (89 : ℝ)/171 ∧ (57 : ℝ)/89 < 1 ∧ 0 < (57 : ℝ)/89 ∧
      ∀ slope : ℝ, 1/((57 : ℝ)/89) < slope → slope < 1/((89 : ℝ)/171) → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · change (1 : ℝ)/3 < (101 : ℝ)/237 ∧ (61 : ℝ)/143 < 1 ∧ 0 < (61 : ℝ)/143 ∧
      ∀ slope : ℝ, 1/((61 : ℝ)/143) < slope → slope < 1/((101 : ℝ)/237) → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨lower,upper⟩)))
  · change (1 : ℝ)/3 < (89 : ℝ)/219 ∧ (57 : ℝ)/137 < 1 ∧ 0 < (57 : ℝ)/137 ∧
      ∀ slope : ℝ, 1/((57 : ℝ)/137) < slope → slope < 1/((89 : ℝ)/219) → GoodSlope slope
    norm_num
    intro slope lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨lower,upper⟩)))

/-- All ten certificate bands now use actual coordinate orientation. In the
second alternative the defining function is read with its coordinates swapped;
the ratio is therefore V/H, not an unsupported assertion about H/V. -/
theorem geometry_log_source_normalized_transfer (n : ℕ) (source : LogSourceData)
    (geometry : source.GeometryChecked n)
    (cornerSigns :
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3) :
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
          nearAxisHorizontal n source.P point.1 ≠ (rational : ℝ)) := by
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
    obtain ⟨k,point,member,goodSlope,irrational⟩ := strict_log_source_normalized_irrational_tangent
      n source.d source.p source.q source.P source.Q _ _ positiveN positiveP positiveQ boundQ
      lowerBand upperBand positiveB good lowerRatio upperRatio lowerCorner upperCorner
    exact ⟨k,point,member,Or.inl ⟨goodSlope,irrational⟩⟩
  · obtain ⟨lowerBand,upperBand,positiveB,good⟩ := reciprocal_log_band_properties source.band (by omega)
    obtain ⟨k,point,member,goodSlope,irrational⟩ := reciprocal_strict_log_source_normalized_irrational_tangent
      n source.d source.p source.q source.P source.Q _ _ positiveN positiveP positiveQ boundQ
      lowerBand upperBand positiveB good lowerRatio upperRatio lowerCorner upperCorner
    exact ⟨k,point,member,Or.inr ⟨goodSlope,irrational⟩⟩

theorem checked_log_source_normalized_transfer (n exponent : ℕ) (source : LogSourceData)
    (geometry : source.GeometryChecked n) (checked : source.LogChecked n exponent) :
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
          nearAxisHorizontal n source.P point.1 ≠ (rational : ℝ)) := by
  exact geometry_log_source_normalized_transfer n source geometry checked.real_log_corners

end LambdaCantor.Integer
