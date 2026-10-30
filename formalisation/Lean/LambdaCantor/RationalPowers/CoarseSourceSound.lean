import LambdaCantor.RationalPowers.CoarseWitnessChecks
import LambdaCantor.RationalPowers.SharedLogSourceSound

namespace LambdaCantor.RationalPowers
open Integer

noncomputable section

/-- Coarse acceptance proves positive dimension of the physical fibre.
Both direct and reciprocal bands use the same shifted legal prefix and the
exact rational lattice phase obtained from the accepted width. -/
theorem CoarseWitness.Checked.positive_dimension {witness : CoarseWitness}
    {numerator denominator : ℕ} (checked : witness.Checked numerator denominator)
    (coprime : numerator.Coprime denominator) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  obtain ⟨static, width, geometry⟩ := checked
  have accepted := CoarseSourceRow.IntegerWidthChecked.widthAccepted static width
  obtain ⟨phase, horizontal_prefix, vertical_prefix, lower_corner, upper_corner⟩ := accepted.log_source
  obtain ⟨horizontal_positive, vertical_positive, _, _⟩ := static
  have denominator_positive : 0 < denominator := width.2.1
  have horizontal_extended_positive : 0 < witness.row.horizontal*3^witness.shift :=
    Nat.mul_pos horizontal_positive (by positivity)
  have metadata : (witness.sourceRow numerator denominator).MetadataChecked := by
    exact ⟨width.1, denominator_positive, horizontal_extended_positive, vertical_positive,
      coprime, horizontal_prefix, vertical_prefix, geometry.2.2.2.2.1, by change (0 : ℕ) < 8033550; norm_num⟩
  have ratios := SharedLogRow.GeometryChecked.real_ratios geometry metadata
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  have exponent_gt_one : 1 < (numerator : ℝ)/denominator := by
    apply (lt_div_iff₀ denominator_real_positive).mpr
    have numerator_lower : denominator < numerator := geometry.2.2.1
    have numerator_real_lower : (denominator : ℝ) < numerator := by exact_mod_cast numerator_lower
    simpa only [one_mul] using numerator_real_lower
  have exponent_ne_two : (numerator : ℝ)/denominator ≠ 2 := by
    intro equality
    have numerator_equal : numerator = 2*denominator := by
      exact_mod_cast (div_eq_iff denominator_real_positive.ne').mp equality
    have gcd := coprime.gcd_eq_one
    rw [numerator_equal, Nat.gcd_mul_left_left] at gcd
    have denominator_lower : 2 ≤ denominator := geometry.1
    omega
  have vertical_bound := ternaryPrefix_bound witness.row.vertical 7 vertical_prefix
  let band : Fin 12 := ⟨witness.band, geometry.2.2.2.2.1⟩
  have band_positive := sharedSlopeBand_positive band
  rcases sharedSlopeBand_orientations band with direct | reciprocal
  · exact strict_rational_log_source_positive_dimension numerator denominator phase
      denominator_positive coprime exponent_gt_one exponent_ne_two
      (7+witness.shift) 7 (witness.row.horizontal*3^witness.shift) witness.row.vertical
      (sharedSlopeBand witness.band).lower (sharedSlopeBand witness.band).upper
      horizontal_extended_positive vertical_positive horizontal_prefix vertical_prefix vertical_bound
      direct.2.1 direct.2.2.1 band_positive.2 direct.2.2.2 ratios.1 ratios.2 lower_corner upper_corner
  · exact reciprocal_strict_rational_log_source_positive_dimension numerator denominator phase
      denominator_positive coprime exponent_gt_one exponent_ne_two
      (7+witness.shift) 7 (witness.row.horizontal*3^witness.shift) witness.row.vertical
      (sharedSlopeBand witness.band).lower (sharedSlopeBand witness.band).upper
      horizontal_extended_positive vertical_positive horizontal_prefix vertical_prefix vertical_bound
      reciprocal.2.1 reciprocal.2.2.1 band_positive.2 reciprocal.2.2.2 ratios.1 ratios.2 lower_corner upper_corner

end
end LambdaCantor.RationalPowers
