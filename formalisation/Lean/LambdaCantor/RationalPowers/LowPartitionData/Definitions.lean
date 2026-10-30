import LambdaCantor.RationalPowers.LowPartitionChecks
import LambdaCantor.RationalPowers.SharedLogData.Catalogue
import LambdaCantor.RationalPowers.CoarseCatalogueData
import LambdaCantor.RationalPowers.ExceptionalLowCertificateLookup

namespace LambdaCantor.RationalPowers

def actualLowPartitionPredicate (integerPart residue : ℕ) : Bool :=
  lowPartitionIdentifierAccepted sharedFullSourceBlocks sharedFullOrdinaryEntries
    (coarseCatalogueSelect coarseIntervalCatalogues) exceptionalCertificateCatalogue exceptionalCertificateEntries
    (integerPart*3675+residue)

theorem actualLowSourceCatalogues_checked : lowSourceCataloguesAccepted sharedFullSourceBlocks exceptionalCertificateCatalogue = true := by
  unfold lowSourceCataloguesAccepted
  rw [exceptionalCertificateCatalogue_checked]
  simp only [sharedFullSourceBlocks_row_count, sharedFullSourceBlocks_accepted,
    exceptionalCertificateCatalogue_size, decide_true, Bool.and_self]

end LambdaCantor.RationalPowers
