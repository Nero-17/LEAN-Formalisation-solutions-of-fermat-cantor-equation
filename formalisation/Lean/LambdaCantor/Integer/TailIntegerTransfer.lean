import LambdaCantor.Integer.TailCylinderTransfer
import LambdaCantor.Integer.TailParameterSelection
import LambdaCantor.Integer.TailCoverageDefinition
import Mathlib.Data.Nat.Log

namespace LambdaCantor.Integer

theorem integer_tail_log_source (coverage : TailCoverageCertified) (n : ℕ)
    (largeExponent : 3^15 ≤ n) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 := by
  have positiveN : n ≠ 0 := by
    have : (0 : ℕ) < 3^15 := by positivity
    omega
  have scaleLower := Nat.pow_log_le_self 3 positiveN
  have scaleUpper := Nat.lt_pow_succ_log_self (by decide : 1 < 3) n
  have depthLarge : 15 ≤ Nat.log 3 n := Nat.le_log_of_pow_le (by decide) largeExponent
  have parameterLower : (1 : ℝ) ≤ (n : ℝ)/3^(Nat.log 3 n) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^(Nat.log 3 n))).2
    simpa only [one_mul] using (show (3 : ℝ)^(Nat.log 3 n) ≤ n by exact_mod_cast scaleLower)
  have parameterUpper : (n : ℝ)/3^(Nat.log 3 n) ≤ 3 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^(Nat.log 3 n))).2
    have castUpper : (n : ℝ) < (3 : ℝ)^(Nat.log 3 n+1) := by exact_mod_cast scaleUpper
    rw [pow_succ] at castUpper
    linarith
  obtain ⟨endpoint,cell,first,last,rowMember,endpointPrefix,endpointPositive,
    endpointLower,cellFirst,cellLast,coefficientLower,coefficientUpper⟩ :=
      tail_parameter_cell_selection ((n : ℝ)/3^(Nat.log 3 n)) parameterLower parameterUpper
  obtain ⟨sources,arcs,checked⟩ := coverage (endpoint,first,last) rowMember cell cellFirst cellLast
  have basePrefix : ternaryPrefix (endpoint*3^(Nat.log 3 n-14)) (11+(Nat.log 3 n-14)) = true := by
    simpa only [Nat.add_zero] using ternaryPrefix_append endpoint 0 11 (Nat.log 3 n-14)
      endpointPrefix (ternaryPrefix_zero _)
  have endpointBound : 14580 ≤ endpoint := by
    have realBound : (14580 : ℝ) ≤ endpoint := by norm_num at endpointLower; linarith
    exact_mod_cast realBound
  have powerBound : 3 ≤ 3^(Nat.log 3 n-14) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 3)
      (show 1 ≤ Nat.log 3 n-14 by omega)
  have minimumBound : 1180980 ≤ 27*(endpoint*3^(Nat.log 3 n-14)) := by
    have product := Nat.mul_le_mul endpointBound powerBound
    nlinarith
  have endpointRealPositive : (0 : ℝ) < endpoint := by exact_mod_cast endpointPositive
  have coefficientIdentity : ((n : ℝ)/3^(Nat.log 3 n))/((endpoint : ℝ)/3^11) =
      (n : ℝ)/(27*(endpoint*3^(Nat.log 3 n-14) : ℕ)) := by
    have power : (3 : ℝ)^(Nat.log 3 n) = 3^14*3^(Nat.log 3 n-14) := by
      rw [← pow_add]
      congr 1
      omega
    push_cast
    rw [power]
    field_simp [ne_of_gt endpointRealPositive]
    <;> ring
  rw [coefficientIdentity] at coefficientLower coefficientUpper
  exact tail_cell_to_log_source sources cell arcs checked n
    (endpoint*3^(Nat.log 3 n-14)) (11+(Nat.log 3 n-14))
    (by norm_num at largeExponent; omega) (by positivity) basePrefix minimumBound
    coefficientLower coefficientUpper

/-- The infinite exponent range is reduced solely to the finite packed-cover
acceptance proposition; all analytical source and irrationality steps are proved. -/
theorem integer_tail_normalized_irrational_source (coverage : TailCoverageCertified) (n : ℕ)
    (largeExponent : 3^15 ≤ n) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
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
  obtain ⟨source,geometry,lower,upper⟩ := integer_tail_log_source coverage n largeExponent
  exact ⟨source,geometry,geometry_log_source_normalized_transfer n source geometry ⟨lower,upper⟩⟩

end LambdaCantor.Integer
