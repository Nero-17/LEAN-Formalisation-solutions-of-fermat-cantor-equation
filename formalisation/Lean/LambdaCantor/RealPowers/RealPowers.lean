import LambdaCantor.RealPowers.AllRealCoverage
import LambdaCantor.RationalPowers.LowPartitionData.PositiveDimension
import LambdaCantor.RationalPowers.LargeExponentCachedAllLayers
import LambdaCantor.Certificates.IntegerTailCachedComplete

noncomputable section
namespace LambdaCantor.RealPowers
open RationalPowers

/-- Theorem 3.1 (thm:real-powers), including the identical introduction
assertion. All finite checks are the concrete production acceptance theorems;
the only hypotheses are the real exponent and its strict lower bound. -/
theorem real_powers_positive_dimension (exponent : ℝ) (exponent_gt_one : 1 < exponent) :
    0 < dimH (intersection exponent (1/3)) :=
  all_real_positive_dimension_of_cached_coverage
    sharedFullSourceBlocks sharedFullOrdinaryEntries
    (coarseCatalogueSelect coarseIntervalCatalogues)
    exceptionalCertificateCatalogue exceptionalCertificateEntries
    actualLowSourceCatalogues_checked actualLowPartitionAllBlocks_checked
    largeExponent_cached_grouped_coverage largeExponent_cached_full_coverage
    Integer.integerTailCachedBlocks Integer.integerTailCachedBlocks_cover
    exponent exponent_gt_one

/-- Literal set-builder form of the manuscript's displayed main theorem. -/
theorem real_powers_positive_dimension_set (exponent : ℝ) (exponent_gt_one : 1 < exponent) :
    0 < dimH {point : ℝ × ℝ | point.1 ∈ cantorSet (1/3) ∧
      point.2 ∈ cantorSet (1/3) ∧ point.1 ^ exponent + point.2 ^ exponent = 1} :=
  real_powers_positive_dimension exponent exponent_gt_one

#print axioms real_powers_positive_dimension
#print axioms real_powers_positive_dimension_set

end LambdaCantor.RealPowers
