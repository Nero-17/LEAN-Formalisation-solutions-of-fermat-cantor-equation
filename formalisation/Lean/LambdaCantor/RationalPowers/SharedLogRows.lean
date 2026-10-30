import LambdaCantor.RationalPowers.SharedLogAtoms

namespace LambdaCantor.RationalPowers
open Integer

/-- A compact source row refers to seven shared atoms; the seventh is log 3.
The integer phase is the companion's unscaled J. The actual phase numerator
is J+a*p-b*q, proved below rather than assumed from a success receipt. -/
structure SharedLogRow where
  numerator : ℕ
  denominator : ℕ
  horizontal : ℕ
  vertical : ℕ
  horizontalDepth : ℕ
  verticalDepth : ℕ
  integerPhase : ℤ
  band : ℕ
  lowIndex : ℕ
  numeratorAtom : ℕ
  denominatorAtom : ℕ
  horizontalAtom : ℕ
  horizontalNextAtom : ℕ
  verticalAtom : ℕ
  verticalNextAtom : ℕ
  threeAtom : ℕ
  deriving DecidableEq

def SharedLogRow.ReferencesValid (row : SharedLogRow) (atoms : Array SharedLogAtom) : Prop :=
  row.numeratorAtom < atoms.size ∧ row.denominatorAtom < atoms.size ∧
  row.horizontalAtom < atoms.size ∧ row.horizontalNextAtom < atoms.size ∧
  row.verticalAtom < atoms.size ∧ row.verticalNextAtom < atoms.size ∧ row.threeAtom < atoms.size ∧
  (sharedLogLookup atoms row.numeratorAtom).value = row.numerator ∧
  (sharedLogLookup atoms row.denominatorAtom).value = row.denominator ∧
  (sharedLogLookup atoms row.horizontalAtom).value = row.horizontal ∧
  (sharedLogLookup atoms row.horizontalNextAtom).value = row.horizontal+1 ∧
  (sharedLogLookup atoms row.verticalAtom).value = row.vertical ∧
  (sharedLogLookup atoms row.verticalNextAtom).value = row.vertical+1 ∧
  (sharedLogLookup atoms row.threeAtom).value = 3

instance (row : SharedLogRow) (atoms : Array SharedLogAtom) : Decidable (row.ReferencesValid atoms) := by
  unfold SharedLogRow.ReferencesValid
  infer_instance

def SharedLogRow.MetadataChecked (row : SharedLogRow) : Prop :=
  0 < row.numerator ∧ 0 < row.denominator ∧ 0 < row.horizontal ∧ 0 < row.vertical ∧
  row.numerator.Coprime row.denominator ∧
  ternaryPrefix row.horizontal row.horizontalDepth = true ∧
  ternaryPrefix row.vertical row.verticalDepth = true ∧ row.band < 12 ∧ row.lowIndex < 8033550

instance (row : SharedLogRow) : Decidable row.MetadataChecked := by
  unfold SharedLogRow.MetadataChecked
  infer_instance

def SharedLogRow.CornersChecked (row : SharedLogRow) (atoms : Array SharedLogAtom) : Prop :=
  let phaseBounds := scaleSignedInterval row.integerPhase
    (signedNatInterval (sharedLogLookup atoms row.threeAtom).bounds)
  let exponentBounds := differenceNatIntervals (sharedLogLookup atoms row.numeratorAtom).bounds
    (sharedLogLookup atoms row.denominatorAtom).bounds
  phaseBounds.upper+(row.numerator : ℤ)*(sharedLogLookup atoms row.horizontalAtom).bounds.upper-
    (row.denominator : ℤ)*exponentBounds.lower-
    (row.denominator : ℤ)*(sharedLogLookup atoms row.verticalNextAtom).bounds.lower < 0 ∧
  0 < phaseBounds.lower+(row.numerator : ℤ)*(sharedLogLookup atoms row.horizontalNextAtom).bounds.lower-
    (row.denominator : ℤ)*exponentBounds.upper-
    (row.denominator : ℤ)*(sharedLogLookup atoms row.verticalAtom).bounds.upper

instance (row : SharedLogRow) (atoms : Array SharedLogAtom) : Decidable (row.CornersChecked atoms) := by
  unfold SharedLogRow.CornersChecked
  infer_instance

def SharedLogRow.Checked (row : SharedLogRow) (atoms : Array SharedLogAtom) : Prop :=
  row.ReferencesValid atoms ∧ row.MetadataChecked ∧ row.CornersChecked atoms

instance (row : SharedLogRow) (atoms : Array SharedLogAtom) : Decidable (row.Checked atoms) := by
  unfold SharedLogRow.Checked
  infer_instance

/-- The reference and arithmetic checks certify the two unscaled logarithmic
corners. No logarithm algorithm is rerun for a source row. -/
theorem SharedLogRow.Checked.raw_real_log_corners {row : SharedLogRow} {atoms : Array SharedLogAtom}
    (atoms_checked : ∀ atom ∈ atoms, atom.Checked) (checked : row.Checked atoms) :
    ((row.integerPhase : ℝ)/row.denominator)*Real.log 3+
      ((row.numerator : ℝ)/row.denominator)*Real.log row.horizontal-
      Real.log ((row.numerator : ℝ)/row.denominator)-Real.log (row.vertical+1 : ℝ) < 0 ∧
    0 < ((row.integerPhase : ℝ)/row.denominator)*Real.log 3+
      ((row.numerator : ℝ)/row.denominator)*Real.log (row.horizontal+1 : ℝ)-
      Real.log ((row.numerator : ℝ)/row.denominator)-Real.log row.vertical := by
  obtain ⟨numerator_index, denominator_index, horizontal_index, horizontal_next_index,
    vertical_index, vertical_next_index, three_index, numerator_matches, denominator_matches,
    horizontal_matches, horizontal_next_matches, vertical_matches, vertical_next_matches, three_matches⟩ := checked.1
  obtain ⟨numerator_positive, denominator_positive, horizontal_positive, vertical_positive, _⟩ := checked.2.1
  have numerator_enclosed := sharedLogLookup_encloses atoms atoms_checked row.numeratorAtom row.numerator
    numerator_index numerator_matches
  have denominator_enclosed := sharedLogLookup_encloses atoms atoms_checked row.denominatorAtom row.denominator
    denominator_index denominator_matches
  have horizontal_enclosed := sharedLogLookup_encloses atoms atoms_checked row.horizontalAtom row.horizontal
    horizontal_index horizontal_matches
  have horizontal_next_enclosed := sharedLogLookup_encloses atoms atoms_checked row.horizontalNextAtom (row.horizontal+1)
    horizontal_next_index horizontal_next_matches
  have vertical_enclosed := sharedLogLookup_encloses atoms atoms_checked row.verticalAtom row.vertical
    vertical_index vertical_matches
  have vertical_next_enclosed := sharedLogLookup_encloses atoms atoms_checked row.verticalNextAtom (row.vertical+1)
    vertical_next_index vertical_next_matches
  have horizontal_next_enclosed_real :
      (signedNatInterval (sharedLogLookup atoms row.horizontalNextAtom).bounds).Encloses rationalLogScale
        (Real.log (row.horizontal+1 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using signedNatInterval_sound horizontal_next_enclosed
  have vertical_next_enclosed_real :
      (signedNatInterval (sharedLogLookup atoms row.verticalNextAtom).bounds).Encloses rationalLogScale
        (Real.log (row.vertical+1 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using signedNatInterval_sound vertical_next_enclosed
  have three_enclosed := sharedLogLookup_encloses atoms atoms_checked row.threeAtom 3 three_index three_matches
  have phase_enclosed := scaleSignedInterval_sound row.integerPhase
    (signedNatInterval (sharedLogLookup atoms row.threeAtom).bounds) (Real.log 3)
    (signedNatInterval_sound three_enclosed)
  have exponent_enclosed := differenceNatIntervals_sound _ _ _ _ numerator_enclosed denominator_enclosed
  rw [← Real.log_div (by positivity : (row.numerator : ℝ) ≠ 0)
    (by positivity : (row.denominator : ℝ) ≠ 0)] at exponent_enclosed
  constructor
  · have corner := negative_rational_log_corner (numerator := row.numerator) row.integerPhase
      (by decide : 0 < rationalLogScale) denominator_positive
      (row.horizontal : ℝ) (row.vertical+1 : ℝ) (Real.log ((row.numerator : ℝ)/row.denominator))
      _ _ _ _ phase_enclosed (signedNatInterval_sound horizontal_enclosed)
      vertical_next_enclosed_real exponent_enclosed checked.2.2.1
    simpa only [Nat.cast_add, Nat.cast_one, signedNatInterval] using corner
  · have corner := positive_rational_log_corner (numerator := row.numerator) row.integerPhase
      (by decide : 0 < rationalLogScale) denominator_positive
      (row.horizontal+1 : ℝ) (row.vertical : ℝ) (Real.log ((row.numerator : ℝ)/row.denominator))
      _ _ _ _ phase_enclosed horizontal_next_enclosed_real
      (signedNatInterval_sound vertical_enclosed) exponent_enclosed checked.2.2.2
    simpa only [Nat.cast_add, Nat.cast_one, signedNatInterval] using corner

/-- Changing from integer endpoint logs to normalized endpoint logs shifts
J to J+a*p-b*q. The equality holds for any positive real endpoints. -/
theorem normalize_integer_log_corner (numerator denominator : ℕ) (integerPhase : ℤ)
    (horizontalDepth verticalDepth : ℕ) (horizontal vertical : ℝ)
    (denominator_positive : 0 < denominator) (horizontal_positive : 0 < horizontal)
    (vertical_positive : 0 < vertical) :
    (((integerPhase+(numerator : ℤ)*horizontalDepth-(denominator : ℤ)*verticalDepth : ℤ) : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log (horizontal/3^horizontalDepth)-
      Real.log ((numerator : ℝ)/denominator)-Real.log (vertical/3^verticalDepth) =
    ((integerPhase : ℝ)/denominator)*Real.log 3+
      ((numerator : ℝ)/denominator)*Real.log horizontal-
      Real.log ((numerator : ℝ)/denominator)-Real.log vertical := by
  rw [Real.log_div horizontal_positive.ne' (by positivity : (3 : ℝ)^horizontalDepth ≠ 0),
    Real.log_div vertical_positive.ne' (by positivity : (3 : ℝ)^verticalDepth ≠ 0),
    Real.log_pow, Real.log_pow]
  push_cast
  have denominator_nonzero : (denominator : ℝ) ≠ 0 := by positivity
  field_simp [denominator_nonzero]
  <;> ring

def SharedLogRow.actualPhase (row : SharedLogRow) : ℤ :=
  row.integerPhase+(row.numerator : ℤ)*row.horizontalDepth-(row.denominator : ℤ)*row.verticalDepth

/-- Shared-atom row checks prove the actual normalized real log corners at
the exact rational phase. Native reduction is used only for finite arithmetic. -/
theorem SharedLogRow.Checked.real_log_corners {row : SharedLogRow} {atoms : Array SharedLogAtom}
    (atoms_checked : ∀ atom ∈ atoms, atom.Checked) (checked : row.Checked atoms) :
    ((row.actualPhase : ℝ)/row.denominator)*Real.log 3+
      ((row.numerator : ℝ)/row.denominator)*Real.log ((row.horizontal : ℝ)/3^row.horizontalDepth)-
      Real.log ((row.numerator : ℝ)/row.denominator)-Real.log ((row.vertical+1 : ℝ)/3^row.verticalDepth) < 0 ∧
    0 < ((row.actualPhase : ℝ)/row.denominator)*Real.log 3+
      ((row.numerator : ℝ)/row.denominator)*Real.log ((row.horizontal+1 : ℝ)/3^row.horizontalDepth)-
      Real.log ((row.numerator : ℝ)/row.denominator)-Real.log ((row.vertical : ℝ)/3^row.verticalDepth) := by
  have raw := SharedLogRow.Checked.raw_real_log_corners atoms_checked checked
  obtain ⟨numerator_positive, denominator_positive, horizontal_positive, vertical_positive, _⟩ := checked.2.1
  have horizontal_real_positive : (0 : ℝ) < row.horizontal := by exact_mod_cast horizontal_positive
  have vertical_real_positive : (0 : ℝ) < row.vertical := by exact_mod_cast vertical_positive
  unfold SharedLogRow.actualPhase
  rw [normalize_integer_log_corner row.numerator row.denominator row.integerPhase row.horizontalDepth row.verticalDepth
    row.horizontal (row.vertical+1) denominator_positive horizontal_real_positive (by positivity),
    normalize_integer_log_corner row.numerator row.denominator row.integerPhase row.horizontalDepth row.verticalDepth
      (row.horizontal+1) row.vertical denominator_positive (by positivity) vertical_real_positive]
  exact raw

end LambdaCantor.RationalPowers
