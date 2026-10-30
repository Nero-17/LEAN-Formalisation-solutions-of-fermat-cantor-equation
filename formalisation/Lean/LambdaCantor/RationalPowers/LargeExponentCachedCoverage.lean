import LambdaCantor.RationalPowers.LargeExponentCachedCoverageChecks
import LambdaCantor.RationalPowers.LargeExponentCachedPhaseCheck
import LambdaCantor.RationalPowers.LargeExponentLayerAssembly

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

theorem largeExponentCachedBlocksCoverCheck_select (layer commonDenominator : ℕ)
    (denominators : List ℕ) (blocks : List CertifiedLargeExponentCachedBlock)
    (checked : largeExponentCachedBlocksCoverCheck layer commonDenominator denominators blocks = true)
    (denominator : ℕ) (denominator_member : denominator ∈ denominators)
    (coefficient : ℝ) (coefficient_bounds : coefficient ∈ Set.Icc (1 : ℝ) 3) :
    ∃ block ∈ blocks, ∃ cell ∈ block.cells,
      cell.denominator = denominator ∧ cell.interval.cell.m = layer ∧
      (cell.interval.cell.lower : ℝ) ≤ cell.interval.cell.denominator*coefficient ∧
      cell.interval.cell.denominator*coefficient ≤ (cell.interval.cell.upper : ℝ) := by
  have coverage := (List.all_eq_true.mp checked) denominator denominator_member
  obtain ⟨interval,interval_member,layer_identity,lower,upper⟩ :=
    largeExponent_finiteCoverageCheck_select layer commonDenominator _ coverage
      coefficient coefficient_bounds
  simp only [largeExponentCachedCoverageRows,List.mem_mergeSort] at interval_member
  obtain ⟨cell,cell_member,identity⟩ := List.mem_map.mp interval_member
  subst interval
  have filtered := List.mem_filter.mp cell_member
  obtain ⟨block,block_member,member⟩ := List.mem_flatMap.mp filtered.1
  exact ⟨block,block_member,cell,member,of_decide_eq_true filtered.2,layer_identity,lower,upper⟩

theorem largeExponentCachedBlocksCoverCheck_grouped (layer commonDenominator : ℕ)
    (blocks : List CertifiedLargeExponentCachedBlock)
    (checked : largeExponentCachedBlocksCoverCheck layer commonDenominator (List.range' 2 108) blocks = true)
    (denominator : ℕ) (denominator_member : denominator ∈ List.range' 2 108) :
    LargeExponentGroupedCoverageChecked layer denominator := by
  intro coefficient coefficient_bounds
  obtain ⟨block,block_member,cell,cell_member,denominator_identity,layer_identity,lower,upper⟩ :=
    largeExponentCachedBlocksCoverCheck_select layer commonDenominator _ blocks checked
      denominator denominator_member coefficient coefficient_bounds
  have phase := largeExponentCachedCellsCheck_cell block.context block.table block.table_checked
    block.cells block.cells_checked cell cell_member
  rw [denominator_identity] at phase
  exact ⟨cell.interval.cell,block.table.sources,cell.arcs,layer_identity,phase,lower,upper⟩

theorem largeExponentCachedBlocksCoverCheck_full (layer commonDenominator : ℕ)
    (blocks : List CertifiedLargeExponentCachedBlock)
    (checked : largeExponentCachedBlocksCoverCheck layer commonDenominator [1] blocks = true) :
    FiniteCoverageCertified layer := by
  intro coefficient coefficient_bounds
  obtain ⟨block,block_member,cell,cell_member,denominator_identity,layer_identity,lower,upper⟩ :=
    largeExponentCachedBlocksCoverCheck_select layer commonDenominator _ blocks checked
      1 (by simp) coefficient coefficient_bounds
  have phase := largeExponentCachedCellsCheck_cell block.context block.table block.table_checked
    block.cells block.cells_checked cell cell_member
  rw [denominator_identity,largeExponent_grouped_one_check] at phase
  exact ⟨cell.interval.cell,block.table.sources,cell.arcs,layer_identity,phase,lower,upper⟩

#print axioms largeExponentCachedCellsCheck_cell
#print axioms largeExponentCachedBlocksCoverCheck_grouped
#print axioms largeExponentCachedBlocksCoverCheck_full

end LambdaCantor.RationalPowers
