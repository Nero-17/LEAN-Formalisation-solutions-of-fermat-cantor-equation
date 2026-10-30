import LambdaCantor.RationalPowers.LargeExponentGroupedChecker
import LambdaCantor.RationalPowers.LargeExponentCoverage

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- Every normalized parameter selects exactly one endpoint cell for the
given denominator before the denominator-scaled phase cover is checked. -/
def LargeExponentGroupedCoverageChecked (layer denominator : ℕ) : Prop :=
  ∀ coefficient ∈ Set.Icc (1 : ℝ) 3,
    ∃ cell : FinitePhaseCell, ∃ sources : Array TailPhaseGeometry, ∃ arcs : List FinitePhaseArc,
      cell.m = layer ∧ largeExponentGroupedCellCheck denominator cell sources arcs = true ∧
      (cell.lower : ℝ) ≤ cell.denominator*coefficient ∧
      cell.denominator*coefficient ≤ (cell.upper : ℝ)

theorem largeExponent_normalized_grouped_positive_dimension
    (layer numerator denominator : ℕ) (coverage : LargeExponentGroupedCoverageChecked layer denominator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator)
    (exponent_ne_two : (numerator : ℝ)/denominator ≠ 2)
    (normalized : (((numerator : ℝ)/denominator)/(3 : ℝ)^layer) ∈ Set.Icc (1 : ℝ) 3) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  obtain ⟨cell,sources,arcs,scale,checked,lower,upper⟩ := coverage _ normalized
  rw [← scale] at lower upper
  obtain ⟨source,phaseNumerator,geometry,lower_corner,upper_corner⟩ := largeExponent_grouped_cell_log_source
    denominator cell sources arcs checked ((numerator : ℝ)/denominator) (by linarith) lower upper
  exact largeExponent_source_positive_dimension numerator denominator phaseNumerator
    denominator_positive coprime exponent_gt_one exponent_ne_two source geometry lower_corner upper_corner

/-- The exact low-denominator large-exponent partition. The premises contain
only acceptance of finite phase/checker data, not the article's dimension
conclusion. They remain to be discharged by the generated certificate files. -/
theorem largeExponent_positive_dimension
    (grouped : ∀ layer : ℕ, 7 ≤ layer → layer ≤ 11 →
      ∀ denominator : ℕ, 2 ≤ denominator → denominator ≤ 109 →
        LargeExponentGroupedCoverageChecked layer denominator)
    (finite : ∀ layer : ℕ, 12 ≤ layer → layer ≤ 14 → FiniteCoverageCertified layer)
    (tail : LargeExponentTailCoverageChecked) (numerator denominator : ℕ)
    (denominator_lower : 2 ≤ denominator) (denominator_upper : denominator ≤ 109)
    (coprime : numerator.Coprime denominator)
    (large : (2187 : ℝ) ≤ (numerator : ℝ)/denominator) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  have denominator_positive : 0 < denominator := by omega
  have exponent_gt_one : 1 < (numerator : ℝ)/denominator := by linarith
  have exponent_ne_two : (numerator : ℝ)/denominator ≠ 2 := by linarith
  obtain ⟨layer,layer_large,normalized⟩ := largeExponent_normalized_layer
    (show (3 : ℝ)^7 ≤ (numerator : ℝ)/denominator by norm_num; exact large)
  by_cases grouped_layer : layer ≤ 11
  · exact largeExponent_normalized_grouped_positive_dimension layer numerator denominator
      (grouped layer layer_large grouped_layer denominator denominator_lower denominator_upper)
      denominator_positive coprime exponent_gt_one exponent_ne_two normalized
  · by_cases finite_layer : layer ≤ 14
    · exact largeExponent_normalized_finite_positive_dimension layer numerator denominator
        (finite layer (by omega) finite_layer) denominator_positive coprime exponent_gt_one exponent_ne_two normalized
    · exact largeExponent_normalized_tail_positive_dimension tail numerator denominator layer
        denominator_positive coprime exponent_gt_one exponent_ne_two (by omega) normalized

end LambdaCantor.RationalPowers
