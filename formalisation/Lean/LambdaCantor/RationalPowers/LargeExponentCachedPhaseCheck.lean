import LambdaCantor.RationalPowers.LargeExponentCachedChecks
import LambdaCantor.RationalPowers.LargeExponentGroupedChecker

namespace LambdaCantor.RationalPowers
open Integer

/-- Only the inexpensive phase core is evaluated in a cell block. Its exact
accepted context table supplies the original logarithmic checker by proof. -/
theorem largeExponentCachedCellsCheck_cell (context : FinitePhaseCell)
    (table : LargeExponentCachedTable) (table_checked : table.check context = true)
    (cells : List LargeExponentCachedCell)
    (cells_checked : largeExponentCachedCellsCheck context table cells = true)
    (cell : LargeExponentCachedCell) (membership : cell ∈ cells) :
    largeExponentGroupedCellCheck cell.denominator cell.interval.cell table.sources cell.arcs = true := by
  obtain ⟨analytic,exact_caches⟩ := table.check_sound context table_checked
  have checked := (List.all_eq_true.mp cells_checked) cell membership
  have data : (0 < cell.denominator ∧ cell.interval.cell.Checked ∧
      LargeExponentSamePhaseContext context cell.interval.cell) ∧
      largeExponentGroupedCellCoreCheck cell.denominator cell.interval.cell
        table.sources table.caches cell.arcs = true := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq] using checked
  have caches_identity : table.sources.map (finitePhaseCache context) =
      table.sources.map (finitePhaseCache cell.interval.cell) := by
    congr 1
    funext geometry
    exact largeExponent_same_phase_cache context cell.interval.cell data.1.2.2 geometry
  have analytic_identity : (fun geometry => decide (finitePhaseAnalyticChecked context geometry)) =
      (fun geometry => decide (finitePhaseAnalyticChecked cell.interval.cell geometry)) := by
    funext geometry
    apply decide_eq_decide.mpr
    rw [largeExponent_same_phase_analytic context cell.interval.cell data.1.2.2 geometry]
  rw [analytic_identity] at analytic
  have core := data.2
  rw [exact_caches,caches_identity] at core
  simpa only [largeExponentGroupedCellCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    And.intro data.1.1 (And.intro data.1.2.1 (And.intro analytic core))

end LambdaCantor.RationalPowers
