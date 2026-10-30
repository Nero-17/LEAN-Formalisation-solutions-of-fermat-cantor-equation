import LambdaCantor.RationalPowers.SharedLogRows
import LambdaCantor.RationalPowers.LowIndexEncoding

namespace LambdaCantor.RationalPowers

structure SharedSlopeBand where
  lowerNumerator : ℕ
  lowerDenominator : ℕ
  upperNumerator : ℕ
  upperDenominator : ℕ
  deriving DecidableEq

/-- The six direct and six reciprocal bands used by the pinned companion.
The narrow first band is retained explicitly and will be included in the
first proved GoodSlope band by rational inequalities. -/
def sharedSlopeBand (band : ℕ) : SharedSlopeBand :=
  match band with
  | 0 => ⟨11,9,2027,1624⟩
  | 1 => ⟨89,73,171,137⟩
  | 2 => ⟨101,79,183,143⟩
  | 3 => ⟨89,57,171,89⟩
  | 4 => ⟨143,61,237,101⟩
  | 5 => ⟨137,57,219,89⟩
  | 6 => ⟨1624,2027,9,11⟩
  | 7 => ⟨137,171,73,89⟩
  | 8 => ⟨143,183,79,101⟩
  | 9 => ⟨89,171,57,89⟩
  | 10 => ⟨101,237,61,143⟩
  | 11 => ⟨89,219,57,137⟩
  | _ => ⟨0,0,0,0⟩

def SharedSlopeBand.lower (band : SharedSlopeBand) : ℚ := band.lowerNumerator/band.lowerDenominator

def SharedSlopeBand.upper (band : SharedSlopeBand) : ℚ := band.upperNumerator/band.upperDenominator

/-- Native geometry checking uses integer products, not rational normalization
or a transcendental operation. This predicate is independent of log corners. -/
def SharedLogRow.GeometryChecked (row : SharedLogRow) : Prop :=
  2 ≤ row.denominator ∧ row.denominator ≤ 109 ∧ row.denominator < row.numerator ∧
  row.numerator < 2187*row.denominator ∧ row.band < 12 ∧
  0 < (sharedSlopeBand row.band).lowerDenominator ∧
  0 < (sharedSlopeBand row.band).upperDenominator ∧
  (sharedSlopeBand row.band).lowerNumerator*row.denominator*(row.horizontal+1) <
    (sharedSlopeBand row.band).lowerDenominator*row.numerator*row.vertical ∧
  row.numerator*(sharedSlopeBand row.band).upperDenominator*(row.vertical+1) <
    (sharedSlopeBand row.band).upperNumerator*row.denominator*row.horizontal

instance (row : SharedLogRow) : Decidable row.GeometryChecked := by
  unfold SharedLogRow.GeometryChecked
  infer_instance

/-- The row's claimed identifier must decode to its actual reduced fraction.
The array access is constant-time in native code. A bare in-range identifier
from SharedLogRow.MetadataChecked is deliberately not enough. -/
def SharedLogRow.IndexMatches (row : SharedLogRow) : Prop :=
  row.lowIndex < 8033550 ∧
  lowRationalPairAt (row.lowIndex/3675) (row.lowIndex%3675) = (row.numerator,row.denominator)

instance (row : SharedLogRow) : Decidable row.IndexMatches := by
  unfold SharedLogRow.IndexMatches
  infer_instance

theorem SharedLogRow.IndexMatches.actual_fraction {row : SharedLogRow}
    (checked : row.IndexMatches) (index : LowRationalIndex)
    (queried : row.lowIndex = lowRationalIdentifier index) :
    lowRationalNumerator index = row.numerator ∧ lowRationalDenominator index = row.denominator := by
  have decoded := lowRationalIndex_decode_identifier index
  have integerPart := congrArg (fun value : LowRationalIndex => value.1.val) decoded
  have residue := congrArg (fun value : LowRationalIndex => value.2.val) decoded
  change lowRationalIdentifier index/3675 = index.1.val at integerPart
  change lowRationalIdentifier index%3675 = index.2.val at residue
  have decoded_pair := checked.2
  rw [queried, integerPart, residue, lowRationalPairAt_index] at decoded_pair
  exact ⟨congrArg Prod.fst decoded_pair,congrArg Prod.snd decoded_pair⟩

/-- Integer full-ratio checks recover the actual real derivative interval.
No band assumption is silently obtained from a corner check. -/
theorem SharedLogRow.GeometryChecked.real_ratios {row : SharedLogRow}
    (geometry : row.GeometryChecked) (metadata : row.MetadataChecked) :
    ((sharedSlopeBand row.band).lower : ℝ)/row.vertical <
      ((row.numerator : ℝ)/row.denominator)/(row.horizontal+1) ∧
    ((row.numerator : ℝ)/row.denominator)/row.horizontal <
      ((sharedSlopeBand row.band).upper : ℝ)/(row.vertical+1) := by
  obtain ⟨denominator_lower, denominator_upper, exponent_lower, exponent_upper, band_bound,
    lower_denominator_positive, upper_denominator_positive, lower_product, upper_product⟩ := geometry
  obtain ⟨numerator_positive, denominator_positive, horizontal_positive, vertical_positive, _⟩ := metadata
  have denominator_real_positive : (0 : ℝ) < row.denominator := by exact_mod_cast denominator_positive
  have horizontal_real_positive : (0 : ℝ) < row.horizontal := by exact_mod_cast horizontal_positive
  have vertical_real_positive : (0 : ℝ) < row.vertical := by exact_mod_cast vertical_positive
  have lower_denominator_real_positive : (0 : ℝ) < (sharedSlopeBand row.band).lowerDenominator := by
    exact_mod_cast lower_denominator_positive
  have upper_denominator_real_positive : (0 : ℝ) < (sharedSlopeBand row.band).upperDenominator := by
    exact_mod_cast upper_denominator_positive
  have lower_real : ((sharedSlopeBand row.band).lowerNumerator : ℝ)*row.denominator*(row.horizontal+1) <
      ((sharedSlopeBand row.band).lowerDenominator : ℝ)*row.numerator*row.vertical := by exact_mod_cast lower_product
  have upper_real : (row.numerator : ℝ)*(sharedSlopeBand row.band).upperDenominator*(row.vertical+1) <
      ((sharedSlopeBand row.band).upperNumerator : ℝ)*row.denominator*row.horizontal := by exact_mod_cast upper_product
  constructor
  · simp only [SharedSlopeBand.lower, Rat.cast_div, Rat.cast_natCast, div_div]
    apply (div_lt_div_iff₀ (mul_pos lower_denominator_real_positive vertical_real_positive)
      (mul_pos denominator_real_positive (by positivity))).mpr
    nlinarith
  · simp only [SharedSlopeBand.upper, Rat.cast_div, Rat.cast_natCast, div_div]
    apply (div_lt_div_iff₀ (mul_pos denominator_real_positive horizontal_real_positive)
      (mul_pos upper_denominator_real_positive (by positivity))).mpr
    nlinarith

end LambdaCantor.RationalPowers
