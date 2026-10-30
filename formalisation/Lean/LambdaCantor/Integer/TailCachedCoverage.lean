import LambdaCantor.Integer.TailCachedPhaseCheck
import LambdaCantor.Integer.TailCoverageDefinition

namespace LambdaCantor.Integer

/-- Table acceptance and cell acceptance are separate proofs, so generated
blocks can share one accepted logarithm table without repeating its evaluation. -/
structure CertifiedTailCachedBlock where
  table : TailCachedTable
  cells : List (ℕ × List TailPhaseArc)
  table_checked : table.check = true
  cells_checked : tailCachedCellsCheck table cells = true

def tailCachedBlocksCoverCheck (blocks : List CertifiedTailCachedBlock) : Bool :=
  tailParameterRows.all (fun row =>
    (List.range' row.2.1 (row.2.2 + 1 - row.2.1)).all (fun cell =>
      blocks.any (fun block => block.cells.any (fun entry => decide (entry.1 = cell)))))

/-- Only finite integer identifiers are inspected in this last coverage check.
Every selected identifier retains its own fully checked phase arcs and table. -/
theorem tailCachedBlocksCoverCheck_sound (blocks : List CertifiedTailCachedBlock)
    (checked : tailCachedBlocksCoverCheck blocks = true) : TailCoverageCertified := by
  intro row row_member cell cell_lower cell_upper
  have range_member : cell ∈ List.range' row.2.1 (row.2.2 + 1 - row.2.1) := by
    rw [List.mem_range'_1]
    omega
  have row_checked := (List.all_eq_true.mp checked) row row_member
  have cell_checked := (List.all_eq_true.mp row_checked) cell range_member
  obtain ⟨block, block_member, block_checked⟩ := List.any_eq_true.mp cell_checked
  obtain ⟨entry, entry_member, entry_equal⟩ := List.any_eq_true.mp block_checked
  have identifier_equal : entry.1 = cell := of_decide_eq_true entry_equal
  refine ⟨block.table.sources, entry.2, ?_⟩
  rw [← identifier_equal]
  exact tailCachedCellsCheck_cell block.table block.table_checked block.cells
    block.cells_checked entry entry_member

#print axioms tailCachedBlocksCoverCheck_sound

end LambdaCantor.Integer
