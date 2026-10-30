import LambdaCantor.RationalPowers.LargeExponentGroupedChecks
import LambdaCantor.RationalPowers.LargeExponentContextChecks
import LambdaCantor.Integer.FiniteCoverageChecks
import LambdaCantor.Integer.TailCachedPhaseCheck

namespace LambdaCantor.RationalPowers
open Integer

/-- A packed arc is decoded before the ordinary geometry and phase checker
sees it. Source indices and signed rotations each have a 32-bit field. -/
def decodeLargeExponentCachedArc (encoded : ℕ) : FinitePhaseArc :=
  let rotation := encoded / 4294967296 % 4294967296
  ⟨encoded % 4294967296,
    if rotation % 2 = 0 then (rotation / 2 : ℕ) else -((rotation / 2 : ℕ) : ℤ)-1,
    ⟨encoded / 18446744073709551616 % 14, Nat.mod_lt _ (by decide)⟩⟩

/-- The context is a separate argument so bounded pieces of one immutable
context table can be checked once and then concatenated by proof. -/
structure LargeExponentCachedTable where
  sources : Array TailPhaseGeometry
  caches : Array TailPhaseCache

def LargeExponentCachedTable.check (table : LargeExponentCachedTable)
    (context : FinitePhaseCell) : Bool :=
  table.sources.all (fun geometry => decide (finitePhaseAnalyticChecked context geometry)) &&
    decide (table.caches = table.sources.map (finitePhaseCache context))

theorem LargeExponentCachedTable.check_sound (table : LargeExponentCachedTable)
    (context : FinitePhaseCell) (checked : table.check context = true) :
    table.sources.all (fun geometry => decide (finitePhaseAnalyticChecked context geometry)) = true ∧
      table.caches = table.sources.map (finitePhaseCache context) := by
  simpa only [LargeExponentCachedTable.check,Bool.and_eq_true,decide_eq_true_eq] using checked

def LargeExponentCachedTable.append (first second : LargeExponentCachedTable) : LargeExponentCachedTable :=
  ⟨first.sources ++ second.sources,first.caches ++ second.caches⟩

theorem LargeExponentCachedTable.append_checked (first second : LargeExponentCachedTable)
    (context : FinitePhaseCell) (first_checked : first.check context = true)
    (second_checked : second.check context = true) :
    (first.append second).check context = true := by
  obtain ⟨first_analytic,first_exact⟩ := first.check_sound context first_checked
  obtain ⟨second_analytic,second_exact⟩ := second.check_sound context second_checked
  simp only [LargeExponentCachedTable.check,LargeExponentCachedTable.append,Array.all_append,
    Bool.and_eq_true,decide_eq_true_eq,Array.map_append]
  exact ⟨⟨first_analytic,second_analytic⟩,by rw [first_exact,second_exact]⟩

/-- One denominator and one endpoint cell per entry. The same coefficient
interval may occur for other denominators with independently checked arcs. -/
structure LargeExponentCachedCell where
  interval : FiniteCoverageRow
  denominator : ℕ
  arcs : List FinitePhaseArc

def largeExponentCachedCellsCheck (context : FinitePhaseCell)
    (table : LargeExponentCachedTable) (cells : List LargeExponentCachedCell) : Bool :=
  cells.all (fun cell =>
    decide (0 < cell.denominator ∧ cell.interval.cell.Checked ∧
      LargeExponentSamePhaseContext context cell.interval.cell) &&
    largeExponentGroupedCellCoreCheck cell.denominator cell.interval.cell
      table.sources table.caches cell.arcs)

end LambdaCantor.RationalPowers
