import LambdaCantor.Integer.TailPhaseChecker

namespace LambdaCantor.Integer

deriving instance DecidableEq for TailPhaseCache

/-- Compact candidate data are decoded before the original checker inspects
their geometry, band membership and interval coverage. -/
def decodeTailCachedArc (encoded : ℕ) : TailPhaseArc :=
  ⟨encoded % 65536, ((encoded / 65536 % 65536 : ℕ) : ℤ) - 32768,
    ⟨encoded / 4294967296 % 4, Nat.mod_lt _ (by decide)⟩⟩

/-- A finite table records the exact computed logarithmic intervals. Checking
the table once lets separate cell blocks reuse those intervals. -/
structure TailCachedTable where
  sources : Array TailPhaseGeometry
  caches : Array TailPhaseCache

def TailCachedTable.check (table : TailCachedTable) : Bool :=
  table.sources.all (fun geometry => decide geometry.AnalyticChecked) &&
    decide (table.caches = table.sources.map tailPhaseCache)

theorem TailCachedTable.check_sound (table : TailCachedTable)
    (checked : table.check = true) :
    table.sources.all (fun geometry => decide geometry.AnalyticChecked) = true ∧
      table.caches = table.sources.map tailPhaseCache := by
  simpa only [TailCachedTable.check, Bool.and_eq_true, decide_eq_true_eq] using checked

def TailCachedTable.append (first second : TailCachedTable) : TailCachedTable :=
  ⟨first.sources ++ second.sources, first.caches ++ second.caches⟩

/-- Independently accepted bounded table chunks can be concatenated without
recomputing any logarithms in the proof of the assembled table. -/
theorem TailCachedTable.append_checked (first second : TailCachedTable)
    (first_checked : first.check = true) (second_checked : second.check = true) :
    (first.append second).check = true := by
  obtain ⟨first_analytic, first_exact⟩ := first.check_sound first_checked
  obtain ⟨second_analytic, second_exact⟩ := second.check_sound second_checked
  simp only [TailCachedTable.check, TailCachedTable.append, Array.all_append,
    Bool.and_eq_true, decide_eq_true_eq, Array.map_append]
  exact ⟨⟨first_analytic, second_analytic⟩, by rw [first_exact, second_exact]⟩

def tailCachedCellsCheck (table : TailCachedTable)
    (cells : List (ℕ × List TailPhaseArc)) : Bool :=
  cells.all (fun cell => tailPhaseCellCoreCheck table.sources table.caches cell.1 cell.2)

/-- Acceptance of an explicit cached cell is acceptance of the original exact
checker. Cached intervals introduce no additional analytic assumption. -/
theorem tailCachedCellsCheck_cell (table : TailCachedTable)
    (table_checked : table.check = true) (cells : List (ℕ × List TailPhaseArc))
    (cells_checked : tailCachedCellsCheck table cells = true)
    (cell : ℕ × List TailPhaseArc) (membership : cell ∈ cells) :
    tailPhaseCellCheck table.sources cell.1 cell.2 = true := by
  obtain ⟨analytic_checked, caches_exact⟩ := table.check_sound table_checked
  have core_checked := (List.all_eq_true.mp cells_checked) cell membership
  rw [caches_exact] at core_checked
  simp only [tailPhaseCellCheck, Bool.and_eq_true]
  exact ⟨analytic_checked, core_checked⟩

end LambdaCantor.Integer
