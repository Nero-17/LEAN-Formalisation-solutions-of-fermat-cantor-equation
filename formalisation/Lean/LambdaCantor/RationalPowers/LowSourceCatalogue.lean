import LambdaCantor.RationalPowers.LowSourceLookup
import LambdaCantor.RationalPowers.SharedLogSourceSound

namespace LambdaCantor.RationalPowers

noncomputable section

theorem SharedSourceBlock.accepted_positive_dimension (block : SharedSourceBlock)
    (accepted : block.accepted = true) (row : SharedLogRow) (member : row ∈ block.rows) :
    0 < dimH (intersection ((row.numerator : ℝ)/row.denominator) (1/3)) := by
  have checks : block.atoms.all (fun atom => decide atom.Checked) = true ∧
      block.rows.all (fun row => decide (row.Checked block.atoms) &&
        decide row.GeometryChecked) = true := by
    simpa only [SharedSourceBlock.accepted, Bool.and_eq_true] using accepted
  have atoms_checked : ∀ atom ∈ block.atoms, atom.Checked := by
    simpa only [Array.all_eq_true', decide_eq_true_eq] using checks.1
  have rows_checked : ∀ row ∈ block.rows, row.Checked block.atoms ∧ row.GeometryChecked := by
    simpa only [Array.all_eq_true', Bool.and_eq_true, decide_eq_true_eq] using checks.2
  exact SharedLogRow.Checked.positive_dimension atoms_checked (rows_checked row member).1
    (rows_checked row member).2

/-- Global native atom/row/geometry acceptance and a successful query prove
positive dimension for exactly the queried finite-domain fraction. The
separate IndexMatches computation prevents accepting a row with a wrong a,b. -/
theorem ordinaryIdentifierAccepted_positive_dimension (blocks : Array SharedSourceBlock)
    (entries : Array (IdentifierEntry OrdinaryReference))
    (catalogue_checked : ordinaryCatalogueAccepted blocks = true) (index : LowRationalIndex)
    (accepted : ordinaryIdentifierAccepted blocks entries (lowRationalIdentifier index) = true) :
    0 < dimH (intersection ((lowRationalNumerator index : ℝ)/lowRationalDenominator index) (1/3)) := by
  unfold ordinaryIdentifierAccepted at accepted
  cases result : ordinarySourceLookup blocks entries (lowRationalIdentifier index) with
  | none => simp only [result, Bool.false_eq_true] at accepted
  | some selected =>
    rcases selected with ⟨block,row⟩
    have index_checked : row.lowIndex = lowRationalIdentifier index ∧ row.IndexMatches := by
      simpa only [result, decide_eq_true_eq] using accepted
    have located : block ∈ blocks ∧ row ∈ block.rows := by
      unfold ordinarySourceLookup at result
      cases lookup : identifierLookup entries (lowRationalIdentifier index) with
      | none => simp only [lookup, reduceCtorEq] at result
      | some entry =>
        exact ordinaryReferenceLookup_mem blocks entry.payload block row (by simpa only [lookup] using result)
    have block_checked : block.accepted = true :=
      (Array.all_eq_true'.mp catalogue_checked) block located.1
    have fraction := SharedLogRow.IndexMatches.actual_fraction index_checked.2 index index_checked.1
    rw [fraction.1, fraction.2]
    exact block.accepted_positive_dimension block_checked row located.2

end
end LambdaCantor.RationalPowers
