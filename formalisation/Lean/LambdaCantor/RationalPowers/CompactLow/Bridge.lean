import LambdaCantor.RationalPowers.CompactLow.Validation
import LambdaCantor.RationalPowers.CompactLow.Generic
import LambdaCantor.RationalPowers.LowPartitionExceptionReuse

namespace LambdaCantor.RationalPowers.CompactLow

theorem originalOrdinary_eq_lookup (identifier : Nat) :
    ordinaryIdentifierAccepted sharedFullSourceBlocks sharedFullOrdinaryEntries identifier =
      (identifierLookup sharedFullOrdinaryEntries identifier).isSome := by
  exact Generic.ordinary_eq_lookup_of_all sharedFullSourceBlocks sharedFullOrdinaryEntries
    referenceAccepted (by rfl) references_accepted identifier

def ordinaryAccepted (identifier : Nat) : Bool :=
  (identifierLookup entries identifier).isSome

theorem ordinaryAccepted_eq (identifier : Nat) :
    ordinaryAccepted identifier =
      ordinaryIdentifierAccepted sharedFullSourceBlocks sharedFullOrdinaryEntries identifier := by
  exact Generic.ordinary_keys_eq sharedFullSourceBlocks sharedFullOrdinaryEntries entries
    referenceAccepted (by rfl) references_accepted entries_eq identifier

/-- The full original predicate, including every coarse and exceptional case. -/
def predicate (integerPart residue : Nat) : Bool :=
  coarseIdentifierAccepted (coarseCatalogueSelect coarseIntervalCatalogues) (integerPart*3675+residue) ||
    ordinaryAccepted (integerPart*3675+residue) ||
      LowPartitionExceptionReuse.reusedExceptionalIdentifierAccepted (integerPart*3675+residue)

theorem predicate_eq : predicate = actualLowPartitionPredicate := by
  funext integerPart residue
  simp only [predicate, actualLowPartitionPredicate, lowPartitionIdentifierAccepted,
    ordinaryAccepted_eq, LowPartitionExceptionReuse.reusedExceptionalIdentifierAccepted_eq]

theorem blockCheck_eq (first count : Nat) :
    lowRationalBlockCheck first count predicate =
      lowRationalBlockCheck first count actualLowPartitionPredicate := by
  rw [predicate_eq]

end LambdaCantor.RationalPowers.CompactLow

#check LambdaCantor.RationalPowers.CompactLow.predicate_eq
#check LambdaCantor.RationalPowers.CompactLow.blockCheck_eq
