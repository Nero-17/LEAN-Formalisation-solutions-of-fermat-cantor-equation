import LambdaCantor.RationalPowers.DenominatorGeometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace LambdaCantor.RationalPowers

/-- The exact permitted-phase width for a positive Cantor rectangle. The two
ternary depths cancel, leaving the quantity checked by the denominator cover. -/
theorem log_source_phase_width (exponent horizontal vertical : ℝ) (firstDepth secondDepth : ℕ)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical) :
    (Real.log exponent+Real.log ((vertical+1)/3^secondDepth)-
        exponent*Real.log (horizontal/3^firstDepth))/Real.log 3 -
      (Real.log exponent+Real.log (vertical/3^secondDepth)-
        exponent*Real.log ((horizontal+1)/3^firstDepth))/Real.log 3 =
      (exponent*Real.log (1+1/horizontal)+Real.log (1+1/vertical))/Real.log 3 := by
  have horizontal_identity : 1+1/horizontal = (horizontal+1)/horizontal := by
    field_simp [horizontal_positive.ne']
  have vertical_identity : 1+1/vertical = (vertical+1)/vertical := by
    field_simp [vertical_positive.ne']
  rw [horizontal_identity, vertical_identity]
  rw [Real.log_div (by positivity : vertical+1 ≠ 0) (by positivity : (3 : ℝ)^secondDepth ≠ 0),
    Real.log_div horizontal_positive.ne' (by positivity : (3 : ℝ)^firstDepth ≠ 0),
    Real.log_div vertical_positive.ne' (by positivity : (3 : ℝ)^secondDepth ≠ 0),
    Real.log_div (by positivity : horizontal+1 ≠ 0) (by positivity : (3 : ℝ)^firstDepth ≠ 0),
    Real.log_div (by positivity : horizontal+1 ≠ 0) horizontal_positive.ne',
    Real.log_div (by positivity : vertical+1 ≠ 0) vertical_positive.ne']
  ring

/-- A strict width check constructs an actual rational phase with both strict
logarithmic corner signs. The phase belongs to the correct 1/b lattice;
integer-depth realization is provided by PhaseDepths. -/
theorem strict_log_phase_of_width (exponent horizontal vertical : ℝ)
    (firstDepth secondDepth denominator : ℕ)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (denominator_positive : 0 < denominator)
    (width : 1/(denominator : ℝ) <
      (exponent*Real.log (1+1/horizontal)+Real.log (1+1/vertical))/Real.log 3) :
    ∃ phase : ℤ,
      ((phase : ℝ)/denominator)*Real.log 3+
        exponent*Real.log (horizontal/3^firstDepth)-Real.log exponent-
          Real.log ((vertical+1)/3^secondDepth) < 0 ∧
      0 < ((phase : ℝ)/denominator)*Real.log 3+
        exponent*Real.log ((horizontal+1)/3^firstDepth)-Real.log exponent-
          Real.log (vertical/3^secondDepth) := by
  have width_equation := log_source_phase_width exponent horizontal vertical firstDepth secondDepth
    horizontal_positive vertical_positive
  obtain ⟨phase, above, below⟩ := phase_lattice_point denominator denominator_positive
    ((Real.log exponent+Real.log (vertical/3^secondDepth)-
      exponent*Real.log ((horizontal+1)/3^firstDepth))/Real.log 3)
    ((Real.log exponent+Real.log ((vertical+1)/3^secondDepth)-
      exponent*Real.log (horizontal/3^firstDepth))/Real.log 3)
    (by rwa [width_equation])
  have logarithm_positive : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have lower_cleared := (div_lt_iff₀ logarithm_positive).mp above
  have upper_cleared := (lt_div_iff₀ logarithm_positive).mp below
  exact ⟨phase, by constructor <;> linarith⟩

/-- The large-denominator source construction supplies both strict corners
and the full slope interval at once, for every scaled real exponent. -/
theorem large_denominator_log_source (normalized scale : ℝ)
    (normalized_lower : 1 ≤ normalized) (normalized_upper : normalized ≤ 3)
    (scale_lower : 1 ≤ scale) (firstDepth secondDepth denominator : ℕ)
    (denominator_cutoff : 110 ≤ denominator) :
    ∃ index : Fin 16, ∃ phase : ℤ,
      let source := denominatorSources index
      source.Checked ∧
      (source.lowerSlope : ℝ) < (scale*normalized)*source.vertical/(scale*source.horizontal+1) ∧
      (scale*normalized)*(source.vertical+1)/(scale*source.horizontal) < (source.upperSlope : ℝ) ∧
      ((phase : ℝ)/denominator)*Real.log 3+
        (scale*normalized)*Real.log ((scale*source.horizontal)/3^firstDepth)-Real.log (scale*normalized)-
          Real.log ((source.vertical+1)/3^secondDepth) < 0 ∧
      0 < ((phase : ℝ)/denominator)*Real.log 3+
        (scale*normalized)*Real.log ((scale*source.horizontal+1)/3^firstDepth)-Real.log (scale*normalized)-
          Real.log (source.vertical/3^secondDepth) := by
  obtain ⟨index, checked, lower, upper, width⟩ :=
    scaled_denominator_source normalized scale normalized_lower normalized_upper scale_lower
  have horizontal_positive : (0 : ℝ) < scale*(denominatorSources index).horizontal := by
    have endpoint_positive : (0 : ℝ) < (denominatorSources index).horizontal := by exact_mod_cast checked.1
    exact mul_pos (by linarith) endpoint_positive
  have vertical_positive : (0 : ℝ) < (denominatorSources index).vertical := by exact_mod_cast checked.2.1
  obtain ⟨phase, first_corner, second_corner⟩ := strict_log_phase_of_width
    (scale*normalized) (scale*(denominatorSources index).horizontal)
    ((denominatorSources index).vertical : ℝ) firstDepth secondDepth denominator
    horizontal_positive vertical_positive (by omega)
    (denominator_width_exceeds_spacing denominator denominator_cutoff _ width)
  exact ⟨index, phase, checked, lower, upper, first_corner, second_corner⟩

end LambdaCantor.RationalPowers

