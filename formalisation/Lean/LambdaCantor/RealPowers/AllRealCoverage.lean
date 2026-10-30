import LambdaCantor.RealPowers.ExponentCases
import LambdaCantor.RealPowers.IrrationalPositive
import LambdaCantor.Integer.IntegerPowers
import LambdaCantor.Integer.TailCachedCoverage
import LambdaCantor.RationalPowers.LargeDenominatorPositive
import LambdaCantor.RationalPowers.LowPartitionPositive
import LambdaCantor.RationalPowers.LargeExponentGroupedCoverage

noncomputable section
namespace LambdaCantor.RealPowers
open RationalPowers

/-- Assembly for the production cached coverage endpoints. Each grouped
layer retains its own denominator-dependent phase coverage, while the same
three full layers and certified tail cover also discharge the integer branch.
The low-denominator catalogue and partition checks remain explicit. -/
theorem all_real_positive_dimension_of_cached_coverage
    (blocks : Array SharedSourceBlock) (ordinaryEntries : Array (IdentifierEntry OrdinaryReference))
    (selectCoarse : ℕ → Option CoarseWitness) (exceptions : Array LowExceptionalCertificate)
    (exceptionalEntries : Array (IdentifierEntry ℕ))
    (catalogues_checked : lowSourceCataloguesAccepted blocks exceptions = true)
    (partition_checked : ∀ block : Fin 35,
      lowRationalBlockCheck (64*block.val) (min 64 (2186-64*block.val))
        (fun integerPart residue => lowPartitionIdentifierAccepted blocks ordinaryEntries selectCoarse
          exceptions exceptionalEntries (integerPart*3675+residue)) = true)
    (grouped : ∀ layer : Fin 5, ∀ denominator ∈ List.range' 2 108,
      LargeExponentGroupedCoverageChecked (layer.val+7) denominator)
    (full : ∀ layer : Fin 3, Integer.FiniteCoverageCertified (layer.val+12))
    (tailBlocks : List Integer.CertifiedTailCachedBlock)
    (tail_checked : Integer.tailCachedBlocksCoverCheck tailBlocks = true)
    (exponent : ℝ) (exponent_gt_one : 1 < exponent) :
    0 < dimH (intersection exponent (1/3)) := by
  have low_positive := low_denominator_positive_dimension_of_acceptance blocks ordinaryEntries
    selectCoarse exceptions exceptionalEntries catalogues_checked partition_checked
  have tail : LargeExponentTailCoverageChecked :=
    Integer.tailCachedBlocksCoverCheck_sound tailBlocks tail_checked
  have grouped_coverage (layer : ℕ) (lower : 7 ≤ layer) (upper : layer ≤ 11)
      (denominator : ℕ) (denominator_lower : 2 ≤ denominator)
      (denominator_upper : denominator ≤ 109) :
      LargeExponentGroupedCoverageChecked layer denominator := by
    have coverage := grouped (⟨layer-7, by omega⟩ : Fin 5) denominator
      (by simp only [List.mem_range'_1]; omega)
    simpa only [Nat.sub_add_cancel lower] using coverage
  have full_coverage (layer : ℕ) (lower : 12 ≤ layer) (upper : layer ≤ 14) :
      Integer.FiniteCoverageCertified layer := by
    have coverage := full (⟨layer-12, by omega⟩ : Fin 3)
    simpa only [Nat.sub_add_cancel lower] using coverage
  rcases real_exponent_cases exponent exponent_gt_one with irrational |
      ⟨numerator,lower,equal⟩ | ⟨numerator,denominator,coprime,lower,equal⟩ |
      ⟨numerator,denominator,coprime,member,equal⟩ |
      ⟨numerator,denominator,coprime,denominator_lower,denominator_upper,numerator_lower,numerator_upper,_,equal⟩ |
      ⟨numerator,denominator,coprime,denominator_lower,denominator_upper,large,equal⟩
  · exact irrational_real_power_positive_dimension irrational exponent_gt_one
  · rw [equal]
    exact Integer.integer_powers_positive_dimension
      (by simpa using full ⟨0, by decide⟩)
      (by simpa using full ⟨1, by decide⟩)
      (by simpa using full ⟨2, by decide⟩)
      (show Integer.TailCoverageCertified from tail) numerator lower
  · rw [equal]
    exact large_denominator_rational_positive_dimension numerator denominator coprime lower
      (by rwa [← equal])
  · have bounds : 2 ≤ denominator ∧ denominator ≤ 109 ∧ denominator < numerator ∧
        numerator < 2187*denominator := by
      simp only [rationalExceptionalPairs, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
        ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
    rw [equal]
    exact low_positive numerator denominator bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2 coprime
  · rw [equal]
    exact low_positive numerator denominator denominator_lower denominator_upper
      numerator_lower numerator_upper coprime
  · rw [equal]
    exact largeExponent_positive_dimension grouped_coverage full_coverage tail numerator denominator
      denominator_lower denominator_upper coprime large

end LambdaCantor.RealPowers
