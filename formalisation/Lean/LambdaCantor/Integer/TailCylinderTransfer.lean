import LambdaCantor.Integer.TailCylinderGeometry
import LambdaCantor.Integer.PhaseLogSourceTransfer

namespace LambdaCantor.Integer

theorem tail_centered_ratio (base baseDepth p a : ℕ) (basePositive : 0 < base)
    (depth : 3 ≤ p) :
    ((27*(base : ℝ)+27/2)/(27*base+(a : ℝ)/3^(p-3))) =
      (((base : ℝ)+1/2)/3^baseDepth)/((base*3^p+a)/3^(baseDepth+p)) := by
  have positiveBase : (0 : ℝ) < base := by exact_mod_cast basePositive
  have power : (3 : ℝ)^p = 27*3^(p-3) := by
    rw [show (27 : ℝ) = 3^3 by norm_num,← pow_add]
    congr 1
    omega
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  rw [pow_add]
  field_simp
  rw [power]
  ring

theorem tail_centered_source_identities (n base baseDepth : ℕ)
    (geometry : TailPhaseGeometry) (band : Fin 4) (basePositive : 0 < base)
    (depth : 3 ≤ geometry.p) :
    tailSourceLower (27*base) ((n : ℝ)/(27*base)) geometry =
      centeredSourceLower n (((base : ℝ)+1/2)/3^baseDepth)
        (tailCylinderSource base baseDepth geometry band) ∧
    tailSourceUpper (27*base) ((n : ℝ)/(27*base)) geometry =
      centeredSourceUpper n (((base : ℝ)+1/2)/3^baseDepth)
        (tailCylinderSource base baseDepth geometry band) := by
  have positiveBase : (0 : ℝ) < base := by exact_mod_cast basePositive
  have logNonzero : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have lowerRatio := tail_centered_ratio base baseDepth geometry.p (geometry.a+1) basePositive depth
  have upperRatio := tail_centered_ratio base baseDepth geometry.p geometry.a basePositive depth
  simp only [Nat.cast_add,Nat.cast_one] at lowerRatio
  constructor
  · unfold tailSourceLower tailPhaseRealOffset centeredSourceLower tailCylinderSource tailPhaseLength
    dsimp only
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,add_assoc]
    rw [lowerRatio]
    field_simp [ne_of_gt positiveBase,logNonzero]
    <;> ring
  · unfold tailSourceUpper tailPhaseRealOffset centeredSourceUpper tailCylinderSource tailPhaseLength
    dsimp only
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,add_assoc]
    rw [upperRatio]
    field_simp [ne_of_gt positiveBase,logNonzero]
    <;> ring

/-- A checked tail coefficient cell is now a genuine source for the integer
Fermat exponent, using actual concatenated Cantor prefixes and a natural depth.
No analytic or source-existence assumption remains beyond the finite checker. -/
theorem tail_cell_to_log_source (sources : Array TailPhaseGeometry) (cell : ℕ)
    (arcs : List TailPhaseArc) (checked : tailPhaseCellCheck sources cell arcs = true)
    (n base baseDepth : ℕ) (exponent : 3 ≤ n) (basePositive : 0 < base)
    (basePrefix : ternaryPrefix base baseDepth = true) (large : 1180980 ≤ 27*base)
    (coefficientLower : 2*(cell : ℝ)-1 ≤ 4000*((n : ℝ)/(27*base)))
    (coefficientUpper : 4000*((n : ℝ)/(27*base)) ≤ 2*(cell : ℝ)+1) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 := by
  apply phase_cover_to_log_source n (by omega) (((base : ℝ)+1/2)/3^baseDepth) (by positivity)
  intro phase phaseBounds
  obtain ⟨geometry,band,shift,geometryChecked,lower,upper⟩ := tailPhaseCellCheck_sound
    sources cell arcs checked (27*base) ((n : ℝ)/(27*base)) phase
    (by exact_mod_cast large) (by positivity) coefficientLower coefficientUpper phaseBounds
  have identities := tail_centered_source_identities n base baseDepth geometry band basePositive
    (by have depth := geometryChecked.1; omega)
  refine ⟨tailCylinderSource base baseDepth geometry band,shift,
    tailCylinderSource_geometry n base baseDepth cell geometry band exponent basePositive
      basePrefix large geometryChecked coefficientLower coefficientUpper,?_,?_,?_⟩
  · have nBound : (3 : ℝ) ≤ n := by exact_mod_cast exponent
    have qBound : (162 : ℝ) ≤ geometry.q := by exact_mod_cast geometryChecked.2.2.2.2.2.1
    have product := mul_le_mul nBound qBound (by norm_num : (0 : ℝ) ≤ 162) (by positivity : (0 : ℝ) ≤ n)
    dsimp [tailCylinderSource]
    norm_num at product ⊢
    nlinarith
  · rwa [identities.1] at lower
  · rwa [identities.2] at upper

end LambdaCantor.Integer
