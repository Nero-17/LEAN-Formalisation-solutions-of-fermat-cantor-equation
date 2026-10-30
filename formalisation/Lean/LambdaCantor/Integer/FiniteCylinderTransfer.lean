import LambdaCantor.Integer.FiniteCylinderGeometry
import LambdaCantor.Integer.PhaseLogSourceTransfer

namespace LambdaCantor.Integer

theorem finite_centered_ratio (cell : FinitePhaseCell) (geometry : TailPhaseGeometry)
    (offset : ℕ) (checked : cell.Checked) (depth : cell.height ≤ geometry.p) :
    (((2*finitePhaseCenter cell*finitePhaseLength cell geometry+
      3^cell.height*finitePhaseLength cell geometry : ℕ) : ℝ)/
      (2*finitePhaseCenter cell*finitePhaseLength cell geometry+2*offset : ℕ)) =
    (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height))/
      ((finiteCylinderBase cell*3^geometry.p+offset)/3^((cell.m-cell.height)+geometry.p)) := by
  have basePositive : 0 < finiteCylinderBase cell := by
    unfold finiteCylinderBase
    have positive := checked.2.1
    positivity
  have positiveBase : (0 : ℝ) < finiteCylinderBase cell := by exact_mod_cast basePositive
  have lengthIdentity : (3 : ℝ)^cell.height*3^(geometry.p-cell.height) = 3^geometry.p := by
    rw [← pow_add]
    congr 1
    omega
  rw [finitePhaseCenter_identity cell checked]
  unfold finitePhaseLength
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  rw [pow_add]
  field_simp
  simp only [← lengthIdentity]
  ring

theorem finite_centered_source_identities (cell : FinitePhaseCell)
    (geometry : TailPhaseGeometry) (band : Fin 14) (n : ℕ)
    (checked : cell.Checked) (depth : cell.height ≤ geometry.p) :
    finiteSourceLower cell ((n : ℝ)/3^cell.m) geometry =
      centeredSourceLower n (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height))
        (finiteCylinderSource cell geometry band) ∧
    finiteSourceUpper cell ((n : ℝ)/3^cell.m) geometry =
      centeredSourceUpper n (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height))
        (finiteCylinderSource cell geometry band) := by
  have lowerRatio := finite_centered_ratio cell geometry (geometry.a+1) checked depth
  have upperRatio := finite_centered_ratio cell geometry geometry.a checked depth
  have logNonzero : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  constructor
  · unfold finiteSourceLower finitePhaseRealOffset centeredSourceLower finiteCylinderSource
    dsimp only
    rw [lowerRatio]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    field_simp [logNonzero]
    <;> ring
  · unfold finiteSourceUpper finitePhaseRealOffset centeredSourceUpper finiteCylinderSource
    dsimp only
    rw [upperRatio]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    field_simp [logNonzero]
    <;> ring

/-- An accepted finite phase cell produces actual Cantor-prefix log corners.
The only input about the numerical certificate is the executable checker result. -/
theorem finite_cell_to_log_source (cell : FinitePhaseCell) (sources : Array TailPhaseGeometry)
    (arcs : List FinitePhaseArc) (checked : finitePhaseCellCheck cell sources arcs = true)
    (n : ℕ) (exponent : 3 ≤ n)
    (coefficientLower : (cell.lower : ℝ) ≤ cell.denominator*((n : ℝ)/3^cell.m))
    (coefficientUpper : cell.denominator*((n : ℝ)/3^cell.m) ≤ (cell.upper : ℝ)) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 := by
  have cellChecked : cell.Checked := by
    have conjunction := checked
    simp only [finitePhaseCellCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at conjunction
    exact conjunction.1
  have basePositive : 0 < finiteCylinderBase cell := by
    unfold finiteCylinderBase
    have positive := cellChecked.2.1
    positivity
  apply phase_cover_to_log_source n (by omega)
    (((finiteCylinderBase cell : ℝ)+1/2)/3^(cell.m-cell.height)) (by positivity)
  intro phase phaseBounds
  obtain ⟨geometry,band,shift,geometryChecked,lower,upper⟩ := finitePhaseCellCheck_sound
    cell sources arcs checked ((n : ℝ)/3^cell.m) phase (by positivity)
      coefficientLower coefficientUpper phaseBounds
  have identities := finite_centered_source_identities cell geometry band n cellChecked geometryChecked.1
  refine ⟨finiteCylinderSource cell geometry band,shift,
    finiteCylinderSource_geometry cell geometry band n exponent cellChecked geometryChecked
      coefficientLower coefficientUpper,?_,?_,?_⟩
  · have nBound : (3 : ℝ) ≤ n := by exact_mod_cast exponent
    have qBound : 2*(3 : ℝ)^cell.verticalDepth ≤ geometry.q := by
      exact_mod_cast geometryChecked.2.2.2.2.1
    have product := mul_le_mul nBound qBound (by positivity) (by positivity : (0 : ℝ) ≤ n)
    dsimp [finiteCylinderSource]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity)).2
    rw [pow_succ]
    nlinarith [show (0 : ℝ) < (3 : ℝ)^cell.verticalDepth by positivity]
  · rwa [identities.1] at lower
  · rwa [identities.2] at upper

end LambdaCantor.Integer



