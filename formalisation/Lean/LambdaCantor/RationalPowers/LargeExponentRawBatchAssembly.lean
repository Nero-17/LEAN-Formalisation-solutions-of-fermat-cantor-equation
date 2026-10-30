import LambdaCantor.RationalPowers.LargeExponentRawBatchBridge

namespace LambdaCantor.RationalPowers
open Integer

/-- Table data stay in Std-only arrays. Only the exact logarithm checks and
their proof assembly use this original-checker interface. -/
def RawPhase.originalTable (sources : Array RawPhase.Geometry)
    (caches : Array RawPhase.Cache) : LargeExponentCachedTable :=
  ⟨sources.map RawPhase.Geometry.toGeometry,caches.map RawPhase.Cache.toCache⟩

theorem largeExponent_raw_table_append_checked (context : RawPhase.Cell)
    (firstSources secondSources : Array RawPhase.Geometry)
    (firstCaches secondCaches : Array RawPhase.Cache)
    (first_checked : (RawPhase.originalTable firstSources firstCaches).check context.toCell = true)
    (second_checked : (RawPhase.originalTable secondSources secondCaches).check context.toCell = true) :
    (RawPhase.originalTable (firstSources ++ secondSources) (firstCaches ++ secondCaches)).check
      context.toCell = true := by
  simpa only [RawPhase.originalTable,LargeExponentCachedTable.append,Array.map_append] using
    LargeExponentCachedTable.append_checked
      (RawPhase.originalTable firstSources firstCaches)
      (RawPhase.originalTable secondSources secondCaches) context.toCell first_checked second_checked

theorem largeExponent_raw_cells_append_checked (context : RawPhase.Cell)
    (sources : Array RawPhase.Geometry) (caches : Array RawPhase.Cache)
    (first second : List RawPhase.CachedCell)
    (first_checked : RawPhase.cellsCheck context sources caches first = true)
    (second_checked : RawPhase.cellsCheck context sources caches second = true) :
    RawPhase.cellsCheck context sources caches (first ++ second) = true := by
  simpa only [RawPhase.cellsCheck,List.all_append,Bool.and_eq_true] using
    And.intro first_checked second_checked

#print axioms largeExponent_raw_table_append_checked
#print axioms largeExponent_raw_cells_append_checked

end LambdaCantor.RationalPowers
