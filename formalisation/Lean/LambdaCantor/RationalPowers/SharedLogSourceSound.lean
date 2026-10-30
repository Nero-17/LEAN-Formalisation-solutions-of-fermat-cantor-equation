import LambdaCantor.RationalPowers.SharedLogBandSound
import LambdaCantor.RationalPowers.LogSourcePositiveDimension
import LambdaCantor.RationalPowers.ReciprocalLogSourcePositiveDimension
import LambdaCantor.Integer.PrefixConcatenation

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- All ordinary-source obligations remain explicit and finite: atom cache,
row references/strict corners, and the independently checked derivative band.
The conclusion concerns the actual real-power intersection. -/
theorem SharedLogRow.Checked.positive_dimension {row : SharedLogRow} {atoms : Array SharedLogAtom}
    (atoms_checked : ∀ atom ∈ atoms, atom.Checked) (checked : row.Checked atoms)
    (geometry : row.GeometryChecked) :
    0 < dimH (intersection ((row.numerator : ℝ)/row.denominator) (1/3)) := by
  obtain ⟨numerator_positive, denominator_positive, horizontal_positive, vertical_positive, coprime,
    horizontal_prefix, vertical_prefix, band_bound, _⟩ := checked.2.1
  have ratios := SharedLogRow.GeometryChecked.real_ratios geometry checked.2.1
  obtain ⟨denominator_lower, denominator_upper, numerator_lower, numerator_upper, _, _⟩ := geometry
  have denominator_real_positive : (0 : ℝ) < row.denominator := by exact_mod_cast denominator_positive
  have exponent_gt_one : 1 < (row.numerator : ℝ)/row.denominator := by
    apply (lt_div_iff₀ denominator_real_positive).mpr
    have lower_real : (row.denominator : ℝ) < row.numerator := by exact_mod_cast numerator_lower
    simpa only [one_mul] using lower_real
  have exponent_ne_two : (row.numerator : ℝ)/row.denominator ≠ 2 := by
    intro equality
    have numerator_equal : row.numerator = 2*row.denominator := by
      exact_mod_cast (div_eq_iff denominator_real_positive.ne').mp equality
    have gcd := coprime.gcd_eq_one
    rw [numerator_equal, Nat.gcd_mul_left_left] at gcd
    omega
  have corners := SharedLogRow.Checked.real_log_corners atoms_checked checked
  have vertical_bound := ternaryPrefix_bound row.vertical row.verticalDepth vertical_prefix
  let band : Fin 12 := ⟨row.band,band_bound⟩
  have band_positive := sharedSlopeBand_positive band
  rcases sharedSlopeBand_orientations band with direct | reciprocal
  · exact strict_rational_log_source_positive_dimension row.numerator row.denominator row.actualPhase
      denominator_positive coprime exponent_gt_one exponent_ne_two
      row.horizontalDepth row.verticalDepth row.horizontal row.vertical
      (sharedSlopeBand row.band).lower (sharedSlopeBand row.band).upper
      horizontal_positive vertical_positive horizontal_prefix vertical_prefix vertical_bound
      direct.2.1 direct.2.2.1 band_positive.2 direct.2.2.2 ratios.1 ratios.2 corners.1 corners.2
  · exact reciprocal_strict_rational_log_source_positive_dimension row.numerator row.denominator row.actualPhase
      denominator_positive coprime exponent_gt_one exponent_ne_two
      row.horizontalDepth row.verticalDepth row.horizontal row.vertical
      (sharedSlopeBand row.band).lower (sharedSlopeBand row.band).upper
      horizontal_positive vertical_positive horizontal_prefix vertical_prefix vertical_bound
      reciprocal.2.1 reciprocal.2.2.1 band_positive.2 reciprocal.2.2.2 ratios.1 ratios.2 corners.1 corners.2

/-- A successful indexed lookup may transfer a checked source to that exact
finite-domain exponent only after the separate a,b index match is proved. -/
theorem SharedLogRow.Checked.positive_dimension_at_index {row : SharedLogRow} {atoms : Array SharedLogAtom}
    (atoms_checked : ∀ atom ∈ atoms, atom.Checked) (checked : row.Checked atoms)
    (geometry : row.GeometryChecked) (index_matches : row.IndexMatches)
    (index : LowRationalIndex) (queried : row.lowIndex = lowRationalIdentifier index) :
    0 < dimH (intersection ((lowRationalNumerator index : ℝ)/lowRationalDenominator index) (1/3)) := by
  have fraction := SharedLogRow.IndexMatches.actual_fraction index_matches index queried
  rw [fraction.1, fraction.2]
  exact SharedLogRow.Checked.positive_dimension atoms_checked checked geometry

end LambdaCantor.RationalPowers
