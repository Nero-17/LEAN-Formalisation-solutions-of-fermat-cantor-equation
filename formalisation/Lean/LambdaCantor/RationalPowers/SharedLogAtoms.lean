import LambdaCantor.RationalPowers.FixedLogSources

namespace LambdaCantor.RationalPowers
open Integer

/-- One outward enclosure of an integer logarithm. Numerical interval values
are data; Checked certifies their equality to the proved fixed-point algorithm. -/
structure SharedLogAtom where
  value : ℕ
  reduction : ℕ
  bounds : NatInterval
  deriving DecidableEq

def SharedLogAtom.Checked (atom : SharedLogAtom) : Prop :=
  0 < atom.value ∧ 3^atom.reduction ≤ atom.value ∧
  (logParameter rationalLogScale atom.value (3^atom.reduction)).upper < rationalLogScale ∧
  atom.bounds = logIntegerInterval rationalLogScale atom.value atom.reduction rationalLogTerms

instance (atom : SharedLogAtom) : Decidable atom.Checked := by
  unfold SharedLogAtom.Checked
  infer_instance

theorem SharedLogAtom.Checked.encloses {atom : SharedLogAtom} (checked : atom.Checked) :
    atom.bounds.Encloses rationalLogScale (Real.log atom.value) := by
  rw [checked.2.2.2]
  exact logIntegerInterval_sound rationalLogScale atom.value atom.reduction rationalLogTerms
    (by decide) checked.2.1 checked.2.2.1 (by decide)

def sharedLogLookup (atoms : Array SharedLogAtom) (index : ℕ) : SharedLogAtom :=
  atoms.getD index ⟨0, 0, ⟨0, 0⟩⟩

theorem sharedLogLookup_checked (atoms : Array SharedLogAtom)
    (checked : ∀ atom ∈ atoms, atom.Checked) (index : ℕ) (bound : index < atoms.size) :
    (sharedLogLookup atoms index).Checked := by
  unfold sharedLogLookup
  rw [← Array.getElem_eq_getD (h := bound) ⟨0, 0, ⟨0, 0⟩⟩]
  exact checked _ (Array.getElem_mem ..)

theorem sharedLogLookup_encloses (atoms : Array SharedLogAtom)
    (checked : ∀ atom ∈ atoms, atom.Checked) (index value : ℕ) (bound : index < atoms.size)
    (value_eq : (sharedLogLookup atoms index).value = value) :
    (sharedLogLookup atoms index).bounds.Encloses rationalLogScale (Real.log value) := by
  have enclosed := (sharedLogLookup_checked atoms checked index bound).encloses
  simpa only [value_eq] using enclosed

def signedNatInterval (bounds : NatInterval) : IntInterval :=
  ⟨bounds.lower, bounds.upper⟩

theorem signedNatInterval_sound {scale : ℕ} {bounds : NatInterval} {value : ℝ}
    (enclosed : bounds.Encloses scale value) :
    (signedNatInterval bounds).Encloses scale value := by
  simpa only [signedNatInterval, IntInterval.Encloses, NatInterval.Encloses, Int.cast_natCast] using enclosed

end LambdaCantor.RationalPowers
