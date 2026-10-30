import LambdaCantor.RationalPowers.LowIndexEncoding
import LambdaCantor.RationalPowers.IdentifierLookup

namespace LambdaCantor.RationalPowers

/-- Separate ordinary predicates deliberately expose both index matching and
band geometry. A true log corner alone is not a source certificate. -/
structure LowCoverageChecks where
  coarse : ℕ → Bool
  ordinaryFound : ℕ → Bool
  ordinaryIndexMatches : ℕ → Bool
  ordinaryBandChecked : ℕ → Bool
  ordinaryCornersChecked : ℕ → Bool
  exceptional : ℕ → Bool

def LowCoverageChecks.atIdentifier (checks : LowCoverageChecks) (identifier : ℕ) : Bool :=
  checks.coarse identifier ||
    (checks.ordinaryFound identifier && checks.ordinaryIndexMatches identifier &&
      checks.ordinaryBandChecked identifier && checks.ordinaryCornersChecked identifier) ||
    checks.exceptional identifier

theorem LowCoverageChecks.atIdentifier_cases (checks : LowCoverageChecks) (identifier : ℕ)
    (checked : checks.atIdentifier identifier = true) :
    checks.coarse identifier = true ∨
      (checks.ordinaryFound identifier = true ∧ checks.ordinaryIndexMatches identifier = true ∧
        checks.ordinaryBandChecked identifier = true ∧ checks.ordinaryCornersChecked identifier = true) ∨
      checks.exceptional identifier = true := by
  simpa only [LowCoverageChecks.atIdentifier, Bool.or_eq_true, Bool.and_eq_true, or_assoc, and_assoc] using checked

/-- At most 64 integer parts and 3675 residues are enumerated per block.
The native checker stores no list of eight million source records. -/
def lowRationalBlockCheck (first count : ℕ) (predicate : ℕ → ℕ → Bool) : Bool :=
  (List.range count).all (fun offset => (List.range 3675).all (predicate (first+offset)))

theorem lowRationalBlockCheck_sound (first count : ℕ) (predicate : ℕ → ℕ → Bool)
    (checked : lowRationalBlockCheck first count predicate = true)
    (integerPart residue : ℕ) (lower : first ≤ integerPart) (upper : integerPart < first+count)
    (residue_bound : residue < 3675) : predicate integerPart residue = true := by
  have outer := List.all_eq_true.mp checked (integerPart-first) (List.mem_range.mpr (by omega))
  have inner := List.all_eq_true.mp outer residue (List.mem_range.mpr residue_bound)
  have identity : first+(integerPart-first) = integerPart := by omega
  simpa only [identity] using inner

/-- Thirty-five bounded native block checks exhaust the same complete index
space proved in LowDenominatorIndex; the last block contains ten integer parts. -/
theorem lowRationalBlockChecks_complete (predicate : ℕ → ℕ → Bool)
    (checked : ∀ block : Fin 35,
      lowRationalBlockCheck (64*block.val) (min 64 (2186-64*block.val)) predicate = true)
    (index : LowRationalIndex) : predicate index.1.val index.2.val = true := by
  let block : Fin 35 := ⟨index.1.val/64, by have bound := index.1.isLt; omega⟩
  apply lowRationalBlockCheck_sound (64*block.val) (min 64 (2186-64*block.val)) predicate
    (checked block) index.1.val index.2.val
  · dsimp only [block]
    omega
  · have bound := index.1.isLt
    dsimp only [block]
    omega
  · simpa only [lowResiduePairs_length] using index.2.isLt

/-- This is finite coverage architecture, not a claim that any generated
partition has passed. Each ordinary branch retains explicit band and index
checks, to be connected to the corresponding checked source-row theorem. -/
theorem LowCoverageChecks.coverage_of_blocks (checks : LowCoverageChecks)
    (checked : ∀ block : Fin 35,
      lowRationalBlockCheck (64*block.val) (min 64 (2186-64*block.val))
        (fun integerPart residue => checks.atIdentifier (integerPart*3675+residue)) = true)
    (index : LowRationalIndex) :
    checks.coarse (lowRationalIdentifier index) = true ∨
      (checks.ordinaryFound (lowRationalIdentifier index) = true ∧
        checks.ordinaryIndexMatches (lowRationalIdentifier index) = true ∧
        checks.ordinaryBandChecked (lowRationalIdentifier index) = true ∧
        checks.ordinaryCornersChecked (lowRationalIdentifier index) = true) ∨
      checks.exceptional (lowRationalIdentifier index) = true := by
  apply checks.atIdentifier_cases
  exact lowRationalBlockChecks_complete _ checked index

end LambdaCantor.RationalPowers
