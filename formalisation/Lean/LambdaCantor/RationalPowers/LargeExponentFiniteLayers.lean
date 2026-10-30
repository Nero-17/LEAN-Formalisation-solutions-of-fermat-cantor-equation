import LambdaCantor.RationalPowers.LargeExponentPhase
import LambdaCantor.Integer.FiniteCoverageCertificate

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

theorem largeExponent_finite_centered_identities (cell : FinitePhaseCell)
    (geometry : TailPhaseGeometry) (band : Fin 14) (exponent : ℝ)
    (checked : cell.Checked) (depth : cell.height ≤ geometry.p) :
    finiteSourceLower cell (exponent/3^cell.m) geometry =
      largeExponentCenteredLower exponent
        (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height))
        (finiteCylinderSource cell geometry band) ∧
    finiteSourceUpper cell (exponent/3^cell.m) geometry =
      largeExponentCenteredUpper exponent
        (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height))
        (finiteCylinderSource cell geometry band) := by
  have lower_ratio := finite_centered_ratio cell geometry (geometry.a+1) checked depth
  have upper_ratio := finite_centered_ratio cell geometry geometry.a checked depth
  have logarithm_nonzero : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  constructor
  · unfold finiteSourceLower finitePhaseRealOffset largeExponentCenteredLower finiteCylinderSource
    dsimp only
    rw [lower_ratio]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    field_simp [logarithm_nonzero]
    <;> ring
  · unfold finiteSourceUpper finitePhaseRealOffset largeExponentCenteredUpper finiteCylinderSource
    dsimp only
    rw [upper_ratio]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    field_simp [logarithm_nonzero]
    <;> ring

/-- The old denominator-cleared finite cell inequalities already enclose all
real exponents in the normalized coefficient interval, not only integers. -/
theorem largeExponent_finite_geometry (cell : FinitePhaseCell)
    (geometry : TailPhaseGeometry) (band : Fin 14) (exponent : ℝ)
    (cell_checked : cell.Checked) (checked : finitePhaseGeometryChecked cell geometry band)
    (coefficient_lower : (cell.lower : ℝ) ≤ cell.denominator*(exponent/3^cell.m))
    (coefficient_upper : cell.denominator*(exponent/3^cell.m) ≤ (cell.upper : ℝ)) :
    LargeExponentGeometryChecked exponent (finiteCylinderSource cell geometry band) := by
  obtain ⟨depth,prefix_a,bound_a,prefix_q,lower_q,bound_q,lower,upper⟩ := checked
  have base_positive : 0 < finiteCylinderBase cell := by
    unfold finiteCylinderBase
    have endpoint_positive := cell_checked.2.1
    positivity
  have horizontal_positive : 0 < finiteCylinderBase cell*3^geometry.p+geometry.a := by positivity
  have vertical_positive : 0 < geometry.q := lt_of_lt_of_le (by positivity) lower_q
  have horizontal_prefix := ternaryPrefix_append (finiteCylinderBase cell) geometry.a
    (cell.m-cell.height) geometry.p (finiteCylinderBase_prefix cell cell_checked) prefix_a
  have identity := finiteCylinderSource_identity cell geometry cell_checked depth
  rw [identity] at lower upper
  have denominator_positive : (0 : ℝ) < cell.denominator := by exact_mod_cast cell_checked.2.2.2.1
  rw [← mul_div_assoc] at coefficient_lower coefficient_upper
  have scaled_lower := (le_div_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^cell.m)).1 coefficient_lower
  have scaled_upper := (div_le_iff₀ (by positivity : (0 : ℝ) < (3 : ℝ)^cell.m)).1 coefficient_upper
  have lower_real : ((finitePhaseBand band).1 : ℝ)*cell.denominator*
      ((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a+1) <
      (finitePhaseBand band).2.1*cell.lower*geometry.q*(3 : ℝ)^cell.m := by exact_mod_cast lower
  have upper_real : ((finitePhaseBand band).2.2.2 : ℝ)*cell.upper*(geometry.q+1)*(3 : ℝ)^cell.m <
      (finitePhaseBand band).2.2.1*cell.denominator*
        ((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a) := by exact_mod_cast upper
  have multiplied_lower := mul_le_mul_of_nonneg_left scaled_lower
    (show (0 : ℝ) ≤ (finitePhaseBand band).2.1*geometry.q by positivity)
  have multiplied_upper := mul_le_mul_of_nonneg_left scaled_upper
    (show (0 : ℝ) ≤ (finitePhaseBand band).2.2.2*(geometry.q+1) by positivity)
  have denominators : 0 < (finitePhaseBand band).2.1 ∧ 0 < (finitePhaseBand band).2.2.2 := by
    fin_cases band <;> decide
  have lower_ratio : ((finitePhaseBand band).1 : ℝ)/(finitePhaseBand band).2.1 <
      exponent*geometry.q/((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a+1) := by
    apply (div_lt_div_iff₀ (by exact_mod_cast denominators.1) (by positivity)).2
    apply (mul_lt_mul_iff_left₀ denominator_positive).1
    nlinarith
  have upper_ratio : exponent*(geometry.q+1)/((finiteCylinderBase cell : ℝ)*3^geometry.p+geometry.a) <
      ((finitePhaseBand band).2.2.1 : ℝ)/(finitePhaseBand band).2.2.2 := by
    apply (div_lt_div_iff₀ (by positivity) (by exact_mod_cast denominators.2)).2
    apply (mul_lt_mul_iff_left₀ denominator_positive).1
    nlinarith
  have inclusion := finiteLogBand_inclusion band
  refine ⟨horizontal_positive,vertical_positive,horizontal_prefix,prefix_q,
    ternaryPrefix_bound _ _ horizontal_prefix,bound_q,?_,?_⟩
  · simpa only [finiteCylinderSource,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      using inclusion.1.trans_lt lower_ratio
  · simpa only [finiteCylinderSource,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      using upper_ratio.trans_le inclusion.2

theorem largeExponent_finite_cell_log_source (cell : FinitePhaseCell)
    (sources : Array TailPhaseGeometry) (arcs : List FinitePhaseArc)
    (checked : finitePhaseCellCheck cell sources arcs = true)
    (exponent : ℝ) (exponent_positive : 0 < exponent)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (coefficient_lower : (cell.lower : ℝ) ≤ cell.denominator*(exponent/3^cell.m))
    (coefficient_upper : cell.denominator*(exponent/3^cell.m) ≤ (cell.upper : ℝ)) :
    ∃ source : LogSourceData, ∃ phaseNumerator : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q+1 : ℝ)/3^source.q) < 0 ∧
      0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P+1 : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q : ℝ)/3^source.q) := by
  have cell_checked : cell.Checked := by
    have conjunction := checked
    simp only [finitePhaseCellCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at conjunction
    exact conjunction.1
  have base_positive : 0 < finiteCylinderBase cell := by
    unfold finiteCylinderBase
    have endpoint_positive := cell_checked.2.1
    positivity
  apply largeExponent_phase_cover_log_source exponent
    (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height))
    denominator denominator_positive (by positivity)
  intro phase phase_bounds
  obtain ⟨geometry,band,shift,geometry_checked,lower,upper⟩ := finitePhaseCellCheck_sound
    cell sources arcs checked (exponent/3^cell.m) phase (by positivity)
    coefficient_lower coefficient_upper phase_bounds
  have identities := largeExponent_finite_centered_identities cell geometry band exponent
    cell_checked geometry_checked.1
  refine ⟨finiteCylinderSource cell geometry band,shift,
    largeExponent_finite_geometry cell geometry band exponent cell_checked geometry_checked
      coefficient_lower coefficient_upper,?_,?_⟩
  · rwa [identities.1] at lower
  · rwa [identities.2] at upper

/-- In particular this applies without change to the three continuous
normalized layers 12,13,14 once their executable finite covers are checked. -/
theorem largeExponent_normalized_finite_positive_dimension
    (layer numerator denominator : ℕ) (coverage : FiniteCoverageCertified layer)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (normalized : (((numerator : ℝ)/denominator)/(3 : ℝ)^layer) ∈ Set.Icc (1 : ℝ) 3) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  obtain ⟨cell,sources,arcs,scale,checked,lower,upper⟩ := coverage _ normalized
  rw [← scale] at lower upper
  obtain ⟨source,phaseNumerator,geometry,lower_corner,upper_corner⟩ := largeExponent_finite_cell_log_source
    cell sources arcs checked ((numerator : ℝ)/denominator) (by linarith)
    denominator denominator_positive lower upper
  exact largeExponent_source_positive_dimension numerator denominator phaseNumerator
    denominator_positive coprime exponent_gt_one exponent_ne_two source geometry lower_corner upper_corner

end LambdaCantor.RationalPowers
