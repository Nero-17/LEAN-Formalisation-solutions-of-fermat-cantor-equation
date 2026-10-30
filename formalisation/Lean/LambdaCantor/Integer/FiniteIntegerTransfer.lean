import LambdaCantor.Integer.FiniteCylinderTransfer

namespace LambdaCantor.Integer

/-- Finite, executable phase-cell coverage at one ternary exponent scale.
All analytic source conclusions are discharged by `finite_cell_to_log_source`. -/
def FiniteCoverageCertified (m : ℕ) : Prop :=
  ∀ coefficient ∈ Set.Icc (1 : ℝ) 3,
    ∃ cell : FinitePhaseCell, ∃ sources : Array TailPhaseGeometry,
      ∃ arcs : List FinitePhaseArc,
        cell.m = m ∧ finitePhaseCellCheck cell sources arcs = true ∧
        (cell.lower : ℝ) ≤ cell.denominator*coefficient ∧
        cell.denominator*coefficient ≤ (cell.upper : ℝ)

theorem integer_finite_log_source (m : ℕ) (coverage : FiniteCoverageCertified m)
    (n : ℕ) (exponent : 3 ≤ n) (lowerScale : 3^m ≤ n) (upperScale : n ≤ 3^(m+1)) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 := by
  have lowerReal : (3 : ℝ)^m ≤ n := by exact_mod_cast lowerScale
  have upperReal : (n : ℝ) ≤ (3 : ℝ)^(m+1) := by exact_mod_cast upperScale
  have coefficientBounds : (n : ℝ)/3^m ∈ Set.Icc (1 : ℝ) 3 := by
    constructor
    · apply (le_div_iff₀ (by positivity)).2
      simpa only [one_mul] using lowerReal
    · apply (div_le_iff₀ (by positivity)).2
      simpa only [pow_succ,mul_comm] using upperReal
  obtain ⟨cell,sources,arcs,scale,checked,lower,upper⟩ := coverage _ coefficientBounds
  rw [← scale] at lower upper
  exact finite_cell_to_log_source cell sources arcs checked n exponent lower upper

end LambdaCantor.Integer
