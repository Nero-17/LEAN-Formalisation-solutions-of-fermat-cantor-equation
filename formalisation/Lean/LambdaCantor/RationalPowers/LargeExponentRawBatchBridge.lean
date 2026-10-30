import LambdaCantor.RationalPowers.LargeExponentRawBatchCore
import LambdaCantor.RationalPowers.LargeExponentRawPhaseBridge
import LambdaCantor.RationalPowers.LargeExponentCachedCoverageChecks

namespace LambdaCantor.RationalPowers
open Integer

def RawPhase.CachedCell.toCell (entry : RawPhase.CachedCell) : LargeExponentCachedCell :=
  ⟨⟨entry.cell.toCell,entry.multiplier⟩,entry.denominator,entry.arcs.map RawPhase.Arc.toArc⟩

def RawPhase.Block.toTable (block : RawPhase.Block) : LargeExponentCachedTable :=
  ⟨block.sources.map RawPhase.Geometry.toGeometry,block.caches.map RawPhase.Cache.toCache⟩

theorem largeExponent_raw_same_context_eq (first second : RawPhase.Cell) :
    RawPhase.sameContext first second = LargeExponentSamePhaseContext first.toCell second.toCell := by rfl

theorem largeExponent_raw_cells_check_eq (context : RawPhase.Cell)
    (sources : Array RawPhase.Geometry) (caches : Array RawPhase.Cache)
    (cells : List RawPhase.CachedCell) :
    RawPhase.cellsCheck context sources caches cells =
      largeExponentCachedCellsCheck context.toCell
        ⟨sources.map RawPhase.Geometry.toGeometry,caches.map RawPhase.Cache.toCache⟩
        (cells.map RawPhase.CachedCell.toCell) := by
  unfold RawPhase.cellsCheck largeExponentCachedCellsCheck
  rw [List.all_map]
  apply congrArg (fun predicate => cells.all predicate)
  funext entry
  apply congrArg₂ Bool.and
  · apply decide_eq_decide.mpr
    simp only [Function.comp_def,RawPhase.CachedCell.toCell,
      largeExponent_raw_cell_checked_eq,largeExponent_raw_same_context_eq]
  · exact largeExponent_raw_phase_core_eq entry.denominator entry.cell sources caches entry.arcs

/-- The expensive exact logarithm-table proof remains separate. The other
field is supplied by a Std-only raw native cell check. -/
structure AcceptedLargeExponentRawBlock where
  data : RawPhase.Block
  table_checked : data.toTable.check data.context.toCell = true
  cells_checked : RawPhase.cellsCheck data.context data.sources data.caches data.cells = true

def AcceptedLargeExponentRawBlock.toCertified (block : AcceptedLargeExponentRawBlock) :
    CertifiedLargeExponentCachedBlock where
  context := block.data.context.toCell
  table := block.data.toTable
  cells := block.data.cells.map RawPhase.CachedCell.toCell
  table_checked := block.table_checked
  cells_checked := by
    unfold RawPhase.Block.toTable
    rw [← largeExponent_raw_cells_check_eq]
    exact block.cells_checked

def largeExponent_raw_grid_projection (row : FiniteCoverageRow) : CheapGrid.Row :=
  ⟨row.cell.m,row.cell.denominator,row.cell.lower,row.cell.upper,row.multiplier⟩

theorem largeExponent_raw_certified_cells (blocks : List AcceptedLargeExponentRawBlock) :
    (blocks.map AcceptedLargeExponentRawBlock.toCertified).flatMap
        (fun block => block.cells) =
      ((blocks.map AcceptedLargeExponentRawBlock.data).flatMap RawPhase.Block.cells).map
        RawPhase.CachedCell.toCell := by
  simp only [List.flatMap_map,List.map_flatMap,List.map_map,
    AcceptedLargeExponentRawBlock.toCertified,Function.comp_def]

/-- Sorting transports along the exact five-field grid projection. Endpoint
and phase data remain in their accepted original blocks throughout. -/
theorem largeExponent_raw_coverage_rows_eq (blocks : List AcceptedLargeExponentRawBlock)
    (denominator : Nat) :
    (largeExponentCachedCoverageRows (blocks.map AcceptedLargeExponentRawBlock.toCertified)
      denominator).map largeExponent_raw_grid_projection =
        RawPhase.coverageRows (blocks.map AcceptedLargeExponentRawBlock.data) denominator := by
  unfold largeExponentCachedCoverageRows
  rw [List.map_mergeSort (s := fun first second : CheapGrid.Row =>
    decide (first.lower*first.multiplier ≤ second.lower*second.multiplier)) (by intros; rfl)]
  simp only [RawPhase.coverageRows,largeExponent_raw_certified_cells,List.filter_map,List.map_map,
    RawPhase.CachedCell.toCell,RawPhase.Cell.toCell,RawPhase.CachedCell.gridRow,
    largeExponent_raw_grid_projection,Function.comp_def] <;> rfl

/-- Exact equality to the original outer coverage computation. The proof
does not replace finite acceptance by a real-parameter coverage premise. -/
theorem largeExponent_raw_blocks_cover_check_eq (layer commonDenominator : Nat)
    (denominators : List Nat) (blocks : List AcceptedLargeExponentRawBlock) :
    RawPhase.blocksCoverCheck layer commonDenominator denominators
        (blocks.map AcceptedLargeExponentRawBlock.data) =
      largeExponentCachedBlocksCoverCheck layer commonDenominator denominators
        (blocks.map AcceptedLargeExponentRawBlock.toCertified) := by
  unfold RawPhase.blocksCoverCheck largeExponentCachedBlocksCoverCheck
  congr 1
  funext denominator
  rw [← largeExponent_cheap_grid_cover_eq]
  congr 1
  change (RawPhase.coverageRows (blocks.map AcceptedLargeExponentRawBlock.data) denominator).toArray =
    ((largeExponentCachedCoverageRows (blocks.map AcceptedLargeExponentRawBlock.toCertified)
      denominator).map largeExponent_raw_grid_projection).toArray
  rw [largeExponent_raw_coverage_rows_eq]

#print axioms largeExponent_raw_cells_check_eq
#print axioms largeExponent_raw_blocks_cover_check_eq

end LambdaCantor.RationalPowers
