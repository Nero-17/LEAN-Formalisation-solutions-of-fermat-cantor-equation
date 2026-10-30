import LambdaCantor.RationalPowers.CoarseSourceSound
import LambdaCantor.RationalPowers.LowSourceCatalogue
import LambdaCantor.RationalPowers.LowExceptionalCertificate
import LambdaCantor.RationalPowers.LowPartitionChecks

namespace LambdaCantor.RationalPowers

noncomputable section

theorem coarseIdentifierAccepted_positive_dimension (select : ℕ → Option CoarseWitness)
    (index : LowRationalIndex)
    (accepted : coarseIdentifierAccepted select (lowRationalIdentifier index) = true) :
    0 < dimH (intersection ((lowRationalNumerator index : ℝ)/lowRationalDenominator index) (1/3)) := by
  unfold coarseIdentifierAccepted at accepted
  cases selected : select (lowRationalIdentifier index) with
  | none => simp only [selected, Bool.false_eq_true] at accepted
  | some witness =>
    have checked : witness.Checked (lowRationalNumerator index) (lowRationalDenominator index) := by
      simpa only [selected, lowRationalPairAt_identifier, decide_eq_true_eq] using accepted
    exact checked.positive_dimension (lowRationalIndex_valid index).2.2.2.2

theorem exceptionalIdentifierAccepted_positive_dimension (certificates : Array LowExceptionalCertificate)
    (entries : Array (IdentifierEntry ℕ))
    (certificates_checked : certificates.all (fun certificate => decide certificate.Checked) = true)
    (index : LowRationalIndex)
    (accepted : exceptionalIdentifierAccepted certificates entries (lowRationalIdentifier index) = true) :
    0 < dimH (intersection ((lowRationalNumerator index : ℝ)/lowRationalDenominator index) (1/3)) := by
  unfold exceptionalIdentifierAccepted at accepted
  cases selected : exceptionalSourceLookup certificates entries (lowRationalIdentifier index) with
  | none => simp only [selected, Bool.false_eq_true] at accepted
  | some certificate =>
    have pair_equal : (lowRationalNumerator index,lowRationalDenominator index) =
        (certificate.numerator,certificate.denominator) := by
      simpa only [selected, lowRationalPairAt_identifier, decide_eq_true_eq] using accepted
    have member : certificate ∈ certificates := by
      unfold exceptionalSourceLookup at selected
      cases lookup : identifierLookup entries (lowRationalIdentifier index) with
      | none => simp only [lookup, reduceCtorEq] at selected
      | some entry =>
        simp only [lookup] at selected
        split at selected
        next bound =>
          have equality := Option.some.inj selected
          exact equality ▸ Array.getElem_mem ..
        next => simp only [reduceCtorEq] at selected
    have checked : certificate.Checked := by
      have all_checked : ∀ certificate ∈ certificates, certificate.Checked := by
        simpa only [Array.all_eq_true', decide_eq_true_eq] using certificates_checked
      exact all_checked certificate member
    have numerator_equal := congrArg Prod.fst pair_equal
    have denominator_equal := congrArg Prod.snd pair_equal
    dsimp only at numerator_equal denominator_equal
    rw [numerator_equal, denominator_equal]
    exact checked.positive_dimension

/-- The actual finite partition checker implies actual fibre positivity.
Every native acceptance premise is displayed: no coverage receipt, source
existence oracle or positive-dimension hypothesis replaces any data check. -/
theorem low_denominator_positive_dimension_at_index_of_acceptance
    (blocks : Array SharedSourceBlock) (ordinaryEntries : Array (IdentifierEntry OrdinaryReference))
    (selectCoarse : ℕ → Option CoarseWitness) (exceptions : Array LowExceptionalCertificate)
    (exceptionalEntries : Array (IdentifierEntry ℕ))
    (catalogues_checked : lowSourceCataloguesAccepted blocks exceptions = true)
    (partition_checked : ∀ block : Fin 35,
      lowRationalBlockCheck (64*block.val) (min 64 (2186-64*block.val))
        (fun integerPart residue => lowPartitionIdentifierAccepted blocks ordinaryEntries selectCoarse
          exceptions exceptionalEntries (integerPart*3675+residue)) = true)
    (index : LowRationalIndex) :
    0 < dimH (intersection ((lowRationalNumerator index : ℝ)/lowRationalDenominator index) (1/3)) := by
  have catalogues :
      ((blocks.foldl (fun count block => count+block.rows.size) 0 = 295480 ∧
        ordinaryCatalogueAccepted blocks = true) ∧ exceptions.size = 7) ∧
        exceptions.all (fun certificate => decide certificate.Checked) = true := by
    simpa only [lowSourceCataloguesAccepted, Bool.and_eq_true, decide_eq_true_eq] using catalogues_checked
  have accepted := lowRationalBlockChecks_complete _ partition_checked index
  change lowPartitionIdentifierAccepted blocks ordinaryEntries selectCoarse exceptions exceptionalEntries
    (lowRationalIdentifier index) = true at accepted
  have cases_accepted :
      coarseIdentifierAccepted selectCoarse (lowRationalIdentifier index) = true ∨
      ordinaryIdentifierAccepted blocks ordinaryEntries (lowRationalIdentifier index) = true ∨
      exceptionalIdentifierAccepted exceptions exceptionalEntries (lowRationalIdentifier index) = true := by
    simpa only [lowPartitionIdentifierAccepted, Bool.or_eq_true, or_assoc] using accepted
  rcases cases_accepted with coarse | ordinary | exceptional
  · exact coarseIdentifierAccepted_positive_dimension selectCoarse index coarse
  · exact ordinaryIdentifierAccepted_positive_dimension blocks ordinaryEntries catalogues.1.1.2 index ordinary
  · exact exceptionalIdentifierAccepted_positive_dimension exceptions exceptionalEntries catalogues.2 index exceptional

/-- The finite index completeness theorem removes the index parameter and
covers every reduced low-denominator rational in the manuscript's range. -/
theorem low_denominator_positive_dimension_of_acceptance
    (blocks : Array SharedSourceBlock) (ordinaryEntries : Array (IdentifierEntry OrdinaryReference))
    (selectCoarse : ℕ → Option CoarseWitness) (exceptions : Array LowExceptionalCertificate)
    (exceptionalEntries : Array (IdentifierEntry ℕ))
    (catalogues_checked : lowSourceCataloguesAccepted blocks exceptions = true)
    (partition_checked : ∀ block : Fin 35,
      lowRationalBlockCheck (64*block.val) (min 64 (2186-64*block.val))
        (fun integerPart residue => lowPartitionIdentifierAccepted blocks ordinaryEntries selectCoarse
          exceptions exceptionalEntries (integerPart*3675+residue)) = true)
    (numerator denominator : ℕ) (denominator_lower : 2 ≤ denominator)
    (denominator_upper : denominator ≤ 109) (numerator_lower : denominator < numerator)
    (numerator_upper : numerator < 2187*denominator) (coprime : numerator.Coprime denominator) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  obtain ⟨index,numerator_equal,denominator_equal⟩ := lowRationalIndex_complete numerator denominator
    denominator_lower denominator_upper numerator_lower numerator_upper coprime
  have result := low_denominator_positive_dimension_at_index_of_acceptance blocks ordinaryEntries
    selectCoarse exceptions exceptionalEntries catalogues_checked partition_checked index
  simpa only [numerator_equal,denominator_equal] using result

end
end LambdaCantor.RationalPowers
