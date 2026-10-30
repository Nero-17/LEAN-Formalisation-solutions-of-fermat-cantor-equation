import LambdaCantor.RationalPowers.LowPartitionData.Definitions

/- SOURCE ONLY. No Lean/compiler execution by this agent.
   No active, passed, production, Prepared656E, manifest or queue source changed. -/
namespace LambdaCantor.RationalPowers.LowPartitionExceptionReuse
open LambdaCantor.RationalPowers

/-- Runtime depends only on the original seven small identifier/payload entries.
    Payload bounds and decoded fractions are reused from their existing actual
    acceptance theorem, rather than recomputed or assumed. -/
def reusedExceptionalIdentifierAccepted (identifier : ℕ) : Bool :=
  (identifierLookup exceptionalCertificateEntries identifier).isSome

/-- A successful lookup retains the original payload bound and the exact
    decoded pair. Both are consequences of the existing accepted-entry theorem. -/
theorem successfulLookup_payloadAccepted (identifier : ℕ) (entry : IdentifierEntry ℕ)
    (found : identifierLookup exceptionalCertificateEntries identifier = some entry) :
    ∃ bound : entry.payload < exceptionalCertificateCatalogue.size,
      lowRationalPairAt (identifier/3675) (identifier%3675) =
        ((exceptionalCertificateCatalogue[entry.payload]).numerator,
          (exceptionalCertificateCatalogue[entry.payload]).denominator) := by
  have sound := identifierLookup_sound exceptionalCertificateEntries identifier entry found
  have entryAccepted : exceptionalIdentifierAccepted exceptionalCertificateCatalogue
      exceptionalCertificateEntries entry.identifier = true := by
    have allAccepted := exceptionalCertificateEntries_accepted
    simp only [Array.all_eq_true'] at allAccepted
    exact allAccepted entry sound.1
  have identifierAccepted : exceptionalIdentifierAccepted exceptionalCertificateCatalogue
      exceptionalCertificateEntries identifier = true := by
    simpa only [sound.2] using entryAccepted
  by_cases bound : entry.payload < exceptionalCertificateCatalogue.size
  · refine ⟨bound, ?_⟩
    have pairAccepted : decide
        (lowRationalPairAt (identifier/3675) (identifier%3675) =
          ((exceptionalCertificateCatalogue[entry.payload]).numerator,
            (exceptionalCertificateCatalogue[entry.payload]).denominator)) = true := by
      simpa only [exceptionalIdentifierAccepted, exceptionalSourceLookup, found, dif_pos bound]
        using identifierAccepted
    exact of_decide_eq_true pairAccepted
  · have impossible : false = true := by
      simpa only [exceptionalIdentifierAccepted, exceptionalSourceLookup, found, dif_neg bound]
        using identifierAccepted
    contradiction

/-- Equality on ALL natural identifiers, without a domain assumption.
    The already checked finite theorem remains a proof dependency here. -/
theorem reusedExceptionalIdentifierAccepted_eq (identifier : ℕ) :
    reusedExceptionalIdentifierAccepted identifier =
      exceptionalIdentifierAccepted exceptionalCertificateCatalogue exceptionalCertificateEntries identifier := by
  cases found : identifierLookup exceptionalCertificateEntries identifier with
  | none =>
    simp only [reusedExceptionalIdentifierAccepted, found, Option.isSome_none,
      exceptionalIdentifierAccepted, exceptionalSourceLookup]
  | some entry =>
    obtain ⟨bound, pairAccepted⟩ := successfulLookup_payloadAccepted identifier entry found
    simp [reusedExceptionalIdentifierAccepted, exceptionalIdentifierAccepted,
      exceptionalSourceLookup, found, bound, pairAccepted]

def reusedActualLowPartitionPredicate (integerPart residue : ℕ) : Bool :=
  coarseIdentifierAccepted (coarseCatalogueSelect coarseIntervalCatalogues) (integerPart*3675+residue) ||
    ordinaryIdentifierAccepted sharedFullSourceBlocks sharedFullOrdinaryEntries (integerPart*3675+residue) ||
    reusedExceptionalIdentifierAccepted (integerPart*3675+residue)

theorem reusedActualLowPartitionPredicate_eq :
    reusedActualLowPartitionPredicate = actualLowPartitionPredicate := by
  funext integerPart residue
  simp only [reusedActualLowPartitionPredicate, actualLowPartitionPredicate,
    lowPartitionIdentifierAccepted, reusedExceptionalIdentifierAccepted_eq]

theorem blockCheck_eq (first count : ℕ) :
    lowRationalBlockCheck first count reusedActualLowPartitionPredicate =
      lowRationalBlockCheck first count actualLowPartitionPredicate := by
  rw [reusedActualLowPartitionPredicate_eq]

#print axioms successfulLookup_payloadAccepted
#print axioms reusedExceptionalIdentifierAccepted_eq
#print axioms reusedActualLowPartitionPredicate_eq
#print axioms blockCheck_eq
end LambdaCantor.RationalPowers.LowPartitionExceptionReuse
