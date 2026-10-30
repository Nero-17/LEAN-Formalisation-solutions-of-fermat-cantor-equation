import LambdaCantor.Integer.RankedGraph
namespace LambdaCantor.Integer
/-- Four consecutive labels, encoded in base four. -/
def vertexWindow (digits : ℕ → Fin 4) (n : ℕ) : Fin 256 :=
  ⟨64 * (digits n).val + 16 * (digits (n+1)).val +
     4 * (digits (n+2)).val + (digits (n+3)).val, by
    have := (digits n).isLt
    have := (digits (n+1)).isLt
    have := (digits (n+2)).isLt
    have := (digits (n+3)).isLt
    omega⟩
def wordWindow (digits : ℕ → Fin 4) (n : ℕ) : Fin 1024 :=
  ⟨4 * (vertexWindow digits n).val + (digits (n+4)).val, by
    have := (vertexWindow digits n).isLt
    have := (digits (n+4)).isLt
    omega⟩
theorem wordWindow_div_four (digits : ℕ → Fin 4) (n : ℕ) :
    (wordWindow digits n).val / 4 = (vertexWindow digits n).val := by
  have := (digits (n+4)).isLt
  simp only [wordWindow]
  omega
theorem wordWindow_mod (digits : ℕ → Fin 4) (n : ℕ) :
    (wordWindow digits n).val % 256 = (vertexWindow digits (n+1)).val := by
  have := (digits n).isLt
  have := (digits (n+1)).isLt
  have := (digits (n+2)).isLt
  have := (digits (n+3)).isLt
  have := (digits (n+4)).isLt
  simp only [wordWindow, vertexWindow, Nat.add_assoc, Nat.reduceAdd]
  omega
theorem vertexWindow_first (digits : ℕ → Fin 4) (n : ℕ) :
    (vertexWindow digits n).val / 64 = (digits n).val := by
  have := (digits (n+1)).isLt
  have := (digits (n+2)).isLt
  have := (digits (n+3)).isLt
  simp only [vertexWindow]
  omega
theorem window_edge (edges : List ℕ) (digits : ℕ → Fin 4) (n : ℕ)
    (h : (wordWindow digits n).val ∈ edges) :
    4 * (vertexWindow digits n).val + (vertexWindow digits (n+1)).val % 4 ∈ edges ∧
    (4 * (vertexWindow digits n).val + (vertexWindow digits (n+1)).val % 4) % 256 =
      (vertexWindow digits (n+1)).val := by
  have hl : (vertexWindow digits (n+1)).val % 4 = (digits (n+4)).val := by
    have := (digits (n+4)).isLt
    simp only [vertexWindow, Nat.add_assoc, Nat.reduceAdd]
    omega
  rw [hl]
  exact ⟨h, wordWindow_mod digits n⟩

theorem digits_periodic_of_vertices (digits : ℕ → Fin 4) (start : ℕ)
    (h : ∀ n ≥ start, vertexWindow digits (n+4) = vertexWindow digits n) :
    ∀ n ≥ start, digits (n+4) = digits n := by
  intro n hn
  apply Fin.ext
  rw [← vertexWindow_first digits (n+4), ← vertexWindow_first digits n, h n hn]
end LambdaCantor.Integer
