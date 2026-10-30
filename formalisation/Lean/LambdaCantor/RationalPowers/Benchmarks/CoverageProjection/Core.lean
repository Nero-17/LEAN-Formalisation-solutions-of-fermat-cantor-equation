import LambdaCantor.RationalPowers.Benchmarks.CoverageProjection.LightCore
import LambdaCantor.RationalPowers.LargeExponentRawBatchCore

namespace LambdaCantor.RationalPowers.Benchmarks.CoverageProjection

def projectEntry (entry : RawPhase.CachedCell) : Nat × CheapGrid.Row :=
  (entry.denominator, entry.gridRow)

def projectBlock (block : RawPhase.Block) : List (Nat × CheapGrid.Row) :=
  block.cells.map projectEntry

def projectBlocks (blocks : List RawPhase.Block) : List (Nat × CheapGrid.Row) :=
  blocks.flatMap projectBlock

theorem projectBlocks_eq_map (blocks : List RawPhase.Block) :
    projectBlocks blocks = (blocks.flatMap RawPhase.Block.cells).map projectEntry := by
  exact (List.map_flatMap (f := projectEntry) (g := RawPhase.Block.cells) (l := blocks)).symm

theorem projectBlocks_cons (block : RawPhase.Block) (blocks : List RawPhase.Block) :
    projectBlocks (block :: blocks) = projectBlock block ++ projectBlocks blocks := by
  simp only [projectBlocks, List.flatMap_cons]

theorem projectBlocks_nil : projectBlocks [] = [] := by rfl

theorem projectBlocks_append (first second : List RawPhase.Block) :
    projectBlocks (first ++ second) = projectBlocks first ++ projectBlocks second := by
  simp only [projectBlocks, List.flatMap_append]

/-- No cell validity or phase acceptance is needed: filter and all five Row fields agree. -/
theorem coverageRows_project_eq (blocks : List RawPhase.Block) (denominator : Nat) :
    coverageRows (projectBlocks blocks) denominator = RawPhase.coverageRows blocks denominator := by
  simp only [coverageRows, projectBlocks_eq_map, RawPhase.coverageRows,
    List.filter_map, List.map_map, Function.comp_def, projectEntry]
  rfl

/-- Equality of the whole original Bool for arbitrary inputs and both denominators. -/
theorem blocksCoverCheck_project_eq (blocks : List RawPhase.Block)
    (layer commonDenominator : Nat) (denominators : List Nat) :
    blocksCoverCheck layer commonDenominator denominators (projectBlocks blocks) =
      RawPhase.blocksCoverCheck layer commonDenominator denominators blocks := by
  unfold blocksCoverCheck RawPhase.blocksCoverCheck
  simp only [coverageRows_project_eq]

end LambdaCantor.RationalPowers.Benchmarks.CoverageProjection
