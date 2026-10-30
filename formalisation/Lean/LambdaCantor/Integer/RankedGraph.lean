import Mathlib.Data.Set.Finite.Lemmas
namespace LambdaCantor.Integer
/-- A finite ranked graph whose equal-rank edges follow a permutation of period four. -/
theorem ranked_path_eventually_period_four {Vertex : Type*} [Finite Vertex]
    (edge : Vertex → Vertex → Prop) (rank : Vertex → ℕ) (next : Vertex → Vertex)
    (rank_edges : ∀ v w, edge v w → rank v ≤ rank w)
    (same_rank_edges : ∀ v w, edge v w → rank v = rank w → w = next v)
    (next_four : ∀ v, next (next (next (next v))) = v)
    (path : ℕ → Vertex) (path_edges : ∀ n, edge (path n) (path (n + 1))) :
    ∃ start, ∀ n ≥ start, path (n + 4) = path n := by
  classical
  obtain ⟨v, ⟨start, rfl⟩, maximal⟩ :=
    Set.exists_max_image (Set.range path) rank (Set.toFinite _) ⟨path 0, 0, rfl⟩
  have monotone_rank : Monotone (fun n => rank (path n)) :=
    monotone_nat_of_le_succ (fun n => rank_edges _ _ (path_edges n))
  have stable : ∀ n ≥ start, rank (path n) = rank (path start) := by
    intro n hn
    exact le_antisymm (maximal _ ⟨n, rfl⟩) (monotone_rank hn)
  have step : ∀ n ≥ start, path (n + 1) = next (path n) := by
    intro n hn
    apply same_rank_edges _ _ (path_edges n)
    rw [stable n hn, stable (n + 1) (by omega)]
  refine ⟨start, ?_⟩
  intro n hn
  calc
    path (n + 4) = next (path (n + 3)) := by simpa using step (n + 3) (by omega)
    _ = next (next (path (n + 2))) := by rw [show path (n + 3) = next (path (n + 2)) from by simpa using step (n + 2) (by omega)]
    _ = next (next (next (path (n + 1)))) := by rw [show path (n + 2) = next (path (n + 1)) from by simpa using step (n + 1) (by omega)]
    _ = next (next (next (next (path n)))) := by rw [step n hn]
    _ = path n := next_four _
end LambdaCantor.Integer
