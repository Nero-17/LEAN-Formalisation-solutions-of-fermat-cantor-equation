import LambdaCantor.RationalPowers.LargeExponentPhase
import LambdaCantor.Integer.TailCylinderTransfer

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- The centered finite-logarithmic tail identity is linear in the real
exponent. Only the existing exponent-free cylinder ratio identity is reused. -/
theorem largeExponent_tail_centered_identities (exponent : ℝ) (base baseDepth : ℕ)
    (geometry : TailPhaseGeometry) (band : Fin 4) (base_positive : 0 < base)
    (depth : 3 ≤ geometry.p) :
    tailSourceLower (27*base) (exponent/(27*base)) geometry =
      largeExponentCenteredLower exponent (((base : ℝ)+1/2)/3^baseDepth)
        (tailCylinderSource base baseDepth geometry band) ∧
    tailSourceUpper (27*base) (exponent/(27*base)) geometry =
      largeExponentCenteredUpper exponent (((base : ℝ)+1/2)/3^baseDepth)
        (tailCylinderSource base baseDepth geometry band) := by
  have base_real_positive : (0 : ℝ) < base := by exact_mod_cast base_positive
  have logarithm_nonzero : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have lower_ratio := tail_centered_ratio base baseDepth geometry.p (geometry.a+1) base_positive depth
  have upper_ratio := tail_centered_ratio base baseDepth geometry.p geometry.a base_positive depth
  simp only [Nat.cast_add,Nat.cast_one] at lower_ratio
  constructor
  · unfold tailSourceLower tailPhaseRealOffset largeExponentCenteredLower tailCylinderSource tailPhaseLength
    dsimp only
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,add_assoc]
    rw [lower_ratio]
    field_simp [base_real_positive.ne',logarithm_nonzero]
    <;> ring
  · unfold tailSourceUpper tailPhaseRealOffset largeExponentCenteredUpper tailCylinderSource tailPhaseLength
    dsimp only
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,add_assoc]
    rw [upper_ratio]
    field_simp [base_real_positive.ne',logarithm_nonzero]
    <;> ring

/-- Exact finite tail geometry remains valid at every real coefficient in
the accepted cell. In particular this theorem makes no integrality claim
about the exponent and uses no integer-exponent dimension conclusion. -/
theorem largeExponent_tail_geometry (exponent : ℝ) (base baseDepth cell : ℕ)
    (geometry : TailPhaseGeometry) (band : Fin 4) (base_positive : 0 < base)
    (base_prefix : ternaryPrefix base baseDepth = true)
    (large : 1180980 ≤ 27*base) (checked : geometry.Checked cell band)
    (coefficient_lower : 2*(cell : ℝ)-1 ≤ 4000*(exponent/(27*base)))
    (coefficient_upper : 4000*(exponent/(27*base)) ≤ 2*(cell : ℝ)+1) :
    LargeExponentGeometryChecked exponent (tailCylinderSource base baseDepth geometry band) := by
  have horizontal_prefix := ternaryPrefix_append base geometry.a baseDepth geometry.p
    base_prefix checked.2.2.1
  have horizontal_positive : 0 < base*3^geometry.p+geometry.a := by positivity
  have vertical_positive : 0 < geometry.q := by
    have bound := checked.2.2.2.2.2.1
    omega
  have ratios := checked.real_ratios geometry cell band (27*base) (exponent/(27*base))
    (by exact_mod_cast large) coefficient_lower coefficient_upper
  have inclusion := tailLogBand_inclusion band
  have denominator_identity :
      (27*(base : ℝ))*(tailPhaseLength geometry : ℝ)+geometry.a =
        (base : ℝ)*3^geometry.p+geometry.a := by
    have length_identity : (27 : ℝ)*(tailPhaseLength geometry : ℝ) = (3 : ℝ)^geometry.p := by
      exact_mod_cast tail_length_identity geometry (by have depth := checked.1; omega)
    calc
      _ = (base : ℝ)*(27*tailPhaseLength geometry)+geometry.a := by ring
      _ = _ := by rw [length_identity]
  have cancellation : (exponent/(27*base))*(27*base) = exponent :=
    div_mul_cancel₀ _ (by positivity)
  have first_numerator : (exponent/(27*base))*geometry.q*(27*base) = exponent*geometry.q := by
    calc
      _ = ((exponent/(27*base))*(27*base))*geometry.q := by ring
      _ = _ := by rw [cancellation]
  have second_numerator : (exponent/(27*base))*(geometry.q+1)*(27*base) = exponent*(geometry.q+1) := by
    calc
      _ = ((exponent/(27*base))*(27*base))*(geometry.q+1) := by ring
      _ = _ := by rw [cancellation]
  rw [first_numerator,second_numerator,denominator_identity] at ratios
  refine ⟨horizontal_positive,vertical_positive,horizontal_prefix,checked.2.2.2.2.1,
    ternaryPrefix_bound _ _ horizontal_prefix,checked.2.2.2.2.2.2.1,?_,?_⟩
  · simpa only [tailCylinderSource,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      using inclusion.1.trans ratios.1
  · simpa only [tailCylinderSource,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      using ratios.2.trans inclusion.2

/-- An accepted finite tail phase checker now supplies actual rational-phase
log corners for a real exponent and genuine concatenated Cantor cylinders. -/
theorem largeExponent_tail_cell_log_source
    (sources : Array TailPhaseGeometry) (cell : ℕ) (arcs : List TailPhaseArc)
    (checked : tailPhaseCellCheck sources cell arcs = true)
    (exponent : ℝ) (exponent_positive : 0 < exponent)
    (denominator base baseDepth : ℕ) (denominator_positive : 0 < denominator)
    (base_positive : 0 < base) (base_prefix : ternaryPrefix base baseDepth = true)
    (large : 1180980 ≤ 27*base)
    (coefficient_lower : 2*(cell : ℝ)-1 ≤ 4000*(exponent/(27*base)))
    (coefficient_upper : 4000*(exponent/(27*base)) ≤ 2*(cell : ℝ)+1) :
    ∃ source : LogSourceData, ∃ phaseNumerator : ℤ,
      LargeExponentGeometryChecked exponent source ∧
      ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q+1 : ℝ)/3^source.q) < 0 ∧
      0 < ((phaseNumerator : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((source.P+1 : ℝ)/3^source.p)-Real.log exponent-
          Real.log ((source.Q : ℝ)/3^source.q) := by
  apply largeExponent_phase_cover_log_source exponent (((base : ℝ)+1/2)/3^baseDepth)
    denominator denominator_positive (by positivity)
  intro phase phase_bounds
  obtain ⟨geometry,band,shift,geometry_checked,lower,upper⟩ := tailPhaseCellCheck_sound
    sources cell arcs checked (27*base) (exponent/(27*base)) phase (by exact_mod_cast large)
    (by positivity) coefficient_lower coefficient_upper phase_bounds
  have identities := largeExponent_tail_centered_identities exponent base baseDepth geometry band
    base_positive (by have depth := geometry_checked.1; omega)
  refine ⟨tailCylinderSource base baseDepth geometry band,shift,
    largeExponent_tail_geometry exponent base baseDepth cell geometry band base_positive
      base_prefix large geometry_checked coefficient_lower coefficient_upper,?_,?_⟩
  · rwa [identities.1] at lower
  · rwa [identities.2] at upper

end LambdaCantor.RationalPowers
