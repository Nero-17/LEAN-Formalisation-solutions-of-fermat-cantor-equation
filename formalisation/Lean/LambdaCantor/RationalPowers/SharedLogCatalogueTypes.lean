import LambdaCantor.RationalPowers.SharedLogGeometry

namespace LambdaCantor.RationalPowers

structure SharedSourceBlock where
  atoms : Array SharedLogAtom
  rows : Array SharedLogRow

structure OrdinaryReference where
  block : ℕ
  row : ℕ
  deriving DecidableEq

def SharedSourceBlock.accepted (block : SharedSourceBlock) : Bool :=
  block.atoms.all (fun atom => decide atom.Checked) &&
    block.rows.all (fun row => decide (row.Checked block.atoms) && decide row.GeometryChecked)

def ordinaryCatalogueAccepted (blocks : Array SharedSourceBlock) : Bool :=
  blocks.all SharedSourceBlock.accepted

/-- Assemble native row acceptance with the already proved atom acceptance;
the logarithm algorithm is not evaluated a second time for a row module. -/
theorem SharedSourceBlock.accepted_of_checks (block : SharedSourceBlock)
    (atoms_checked : block.atoms.all (fun atom => decide atom.Checked) = true)
    (rows_checked : block.rows.all (fun row =>
      decide (row.Checked block.atoms) && decide row.GeometryChecked && decide row.IndexMatches) = true) :
    block.accepted = true := by
  have checked : ∀ row ∈ block.rows,
      row.Checked block.atoms ∧ row.GeometryChecked ∧ row.IndexMatches := by
    simpa only [Array.all_eq_true', Bool.and_eq_true, decide_eq_true_eq, and_assoc]
      using rows_checked
  have retained : ∀ row ∈ block.rows, row.Checked block.atoms ∧ row.GeometryChecked := by
    intro row member
    exact ⟨(checked row member).1, (checked row member).2.1⟩
  have rows_accepted : block.rows.all (fun row =>
      decide (row.Checked block.atoms) && decide row.GeometryChecked) = true := by
    simpa only [Array.all_eq_true', Bool.and_eq_true, decide_eq_true_eq] using retained
  simpa only [SharedSourceBlock.accepted, Bool.and_eq_true] using
    And.intro atoms_checked rows_accepted

end LambdaCantor.RationalPowers
