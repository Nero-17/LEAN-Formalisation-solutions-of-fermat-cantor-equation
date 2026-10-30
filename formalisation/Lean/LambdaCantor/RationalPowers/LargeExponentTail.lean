import LambdaCantor.RationalPowers.LargeExponentTailGeometry
import LambdaCantor.Integer.TailParameterSelection

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- Only executable finite checker acceptance is required here. Actual
logarithmic corners, real-power sources and dimension are proved downstream. -/
def LargeExponentTailCoverageChecked : Prop :=
  ∀ row ∈ tailParameterRows, ∀ cell : ℕ, row.2.1 ≤ cell → cell ≤ row.2.2 →
    ∃ sources : Array TailPhaseGeometry, ∃ arcs : List TailPhaseArc,
      tailPhaseCellCheck sources cell arcs = true

/-- The old finite phase and legal-prefix data apply to every real normalized
parameter in [1,3], uniformly for all natural layers m≥15. -/
theorem largeExponent_normalized_tail_log_source
    (coverage : LargeExponentTailCoverageChecked) (exponent : ℝ)
    (layer denominator : ℕ) (layer_large : 15 ≤ layer)
    (denominator_positive : 0 < denominator)
    (normalized : exponent/(3 : ℝ)^layer ∈ Set.Icc (1 : ℝ) 3) :
    ∃ source : LogSourceData, ∃ phaseNumerator : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q+1 : ℝ)/3^source.q) < 0 ∧
      0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P+1 : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q : ℝ)/3^source.q) := by
  have exponent_positive : 0 < exponent := by
    have scale_positive : (0 : ℝ) < (3 : ℝ)^layer := by positivity
    have lower := (le_div_iff₀ scale_positive).1 normalized.1
    linarith
  obtain ⟨endpoint,cell,first,last,row_member,endpoint_prefix,endpoint_positive,
    endpoint_lower,cell_first,cell_last,coefficient_lower,coefficient_upper⟩ :=
      tail_parameter_cell_selection (exponent/(3 : ℝ)^layer) normalized.1 normalized.2
  obtain ⟨sources,arcs,checked⟩ := coverage (endpoint,first,last) row_member cell cell_first cell_last
  have base_prefix : ternaryPrefix (endpoint*3^(layer-14)) (11+(layer-14)) = true := by
    simpa only [Nat.add_zero] using ternaryPrefix_append endpoint 0 11 (layer-14)
      endpoint_prefix (ternaryPrefix_zero _)
  have endpoint_bound : 14580 ≤ endpoint := by
    have bound : (14580 : ℝ) ≤ endpoint := by norm_num at endpoint_lower; linarith
    exact_mod_cast bound
  have power_bound : 3 ≤ 3^(layer-14) := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 3) (show 1 ≤ layer-14 by omega)
  have minimum_bound : 1180980 ≤ 27*(endpoint*3^(layer-14)) := by
    have product := Nat.mul_le_mul endpoint_bound power_bound
    nlinarith
  have endpoint_real_positive : (0 : ℝ) < endpoint := by exact_mod_cast endpoint_positive
  have coefficient_identity : (exponent/(3 : ℝ)^layer)/((endpoint : ℝ)/3^11) =
      exponent/(27*(endpoint*3^(layer-14) : ℕ)) := by
    have power_identity : (3 : ℝ)^layer = 3^14*3^(layer-14) := by
      rw [← pow_add]
      congr 1
      omega
    push_cast
    rw [power_identity]
    field_simp [endpoint_real_positive.ne']
    <;> ring
  rw [coefficient_identity] at coefficient_lower coefficient_upper
  exact largeExponent_tail_cell_log_source sources cell arcs checked exponent exponent_positive
    denominator (endpoint*3^(layer-14)) (11+(layer-14)) denominator_positive
    (by positivity) base_prefix minimum_bound coefficient_lower coefficient_upper

/-- The final tail application uses the actual reduced rational exponent and
the proved rational natural-depth realization, not an integer-power theorem. -/
theorem largeExponent_normalized_tail_positive_dimension
    (coverage : LargeExponentTailCoverageChecked) (numerator denominator layer : ℕ)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (layer_large : 15 ≤ layer)
    (normalized : (((numerator : ℝ)/denominator)/(3 : ℝ)^layer) ∈ Set.Icc (1 : ℝ) 3) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  obtain ⟨source,phaseNumerator,geometry,lower,upper⟩ := largeExponent_normalized_tail_log_source
    coverage ((numerator : ℝ)/denominator) layer denominator layer_large denominator_positive normalized
  exact largeExponent_source_positive_dimension numerator denominator phaseNumerator
    denominator_positive coprime exponent_gt_one exponent_ne_two source geometry lower upper

end LambdaCantor.RationalPowers
