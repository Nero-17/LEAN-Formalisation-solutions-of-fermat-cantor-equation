import LambdaCantor.RationalPowers.LargeExponentRawBatchBridge
import LambdaCantor.RationalPowers.LargeExponentCachedCoverage

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

theorem largeExponent_raw_blocks_grouped_coverage (layer commonDenominator : Nat)
    (blocks : List AcceptedLargeExponentRawBlock)
    (checked : RawPhase.blocksCoverCheck layer commonDenominator (List.range' 2 108)
      (blocks.map AcceptedLargeExponentRawBlock.data) = true)
    (denominator : Nat) (membership : denominator ∈ List.range' 2 108) :
    LargeExponentGroupedCoverageChecked layer denominator := by
  apply largeExponentCachedBlocksCoverCheck_grouped layer commonDenominator
    (blocks.map AcceptedLargeExponentRawBlock.toCertified) _ denominator membership
  rw [← largeExponent_raw_blocks_cover_check_eq]
  exact checked

theorem largeExponent_raw_blocks_full_coverage (layer commonDenominator : Nat)
    (blocks : List AcceptedLargeExponentRawBlock)
    (checked : RawPhase.blocksCoverCheck layer commonDenominator [1]
      (blocks.map AcceptedLargeExponentRawBlock.data) = true) : FiniteCoverageCertified layer := by
  apply largeExponentCachedBlocksCoverCheck_full layer commonDenominator
    (blocks.map AcceptedLargeExponentRawBlock.toCertified)
  rw [← largeExponent_raw_blocks_cover_check_eq]
  exact checked

#print axioms largeExponent_raw_blocks_grouped_coverage
#print axioms largeExponent_raw_blocks_full_coverage

end LambdaCantor.RationalPowers
