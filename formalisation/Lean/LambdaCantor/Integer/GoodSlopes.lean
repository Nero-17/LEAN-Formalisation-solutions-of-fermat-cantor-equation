import LambdaCantor.Certificates.IntegerFeasibility0
import LambdaCantor.Certificates.IntegerFeasibility1
import LambdaCantor.Certificates.IntegerFeasibility2
import LambdaCantor.Certificates.IntegerFeasibility3
import LambdaCantor.Certificates.IntegerFeasibility4
import LambdaCantor.Integer.Windows
import LambdaCantor.Integer.VanishingErrors

namespace LambdaCantor.Integer

/-- The five certified open slope bands printed in Lemma good-slopes. -/
def GoodSlope (r : ℝ) : Prop :=
  (89 / 73 < r ∧ r < 171 / 137) ∨
  (101 / 79 < r ∧ r < 183 / 143) ∨
  (89 / 57 < r ∧ r < 171 / 89) ∨
  (143 / 61 < r ∧ r < 237 / 101) ∨
  (137 / 57 < r ∧ r < 219 / 89)

/-- An eventually retained sliding-window word sequence gives an eventually
periodic digit sequence. All graph hypotheses are explicit in this reusable step. -/
theorem digits_periodic_of_eventually_retained
    (edges : List ℕ) (rank : Fin 256 → ℕ) (next : Fin 256 → Fin 256)
    (rank_edges : ∀ v w : Fin 256,
      (4 * v.val + w.val % 4 ∈ edges ∧
        (4 * v.val + w.val % 4) % 256 = w.val) → rank v ≤ rank w)
    (same_rank_edges : ∀ v w : Fin 256,
      (4 * v.val + w.val % 4 ∈ edges ∧
        (4 * v.val + w.val % 4) % 256 = w.val) →
      rank v = rank w → w = next v)
    (next_four : ∀ v, next (next (next (next v))) = v)
    (digits : ℕ → Fin 4)
    (retained : ∃ start, ∀ n ≥ start, (wordWindow digits n).val ∈ edges) :
    ∃ start, ∀ n ≥ start, digits (n + 4) = digits n := by
  obtain ⟨start, hstart⟩ := retained
  obtain ⟨later, hlater⟩ := ranked_path_eventually_period_four
    (fun v w : Fin 256 => 4 * v.val + w.val % 4 ∈ edges ∧
      (4 * v.val + w.val % 4) % 256 = w.val)
    rank next rank_edges same_rank_edges next_four
    (fun n => vertexWindow digits (start+n)) (by
      intro n
      simpa only [Nat.add_assoc] using
        window_edge edges digits (start+n) (hstart (start+n) (by omega)))
  refine ⟨start + later, digits_periodic_of_vertices digits (start+later) ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show start ≤ n by omega)
  simpa only [Nat.add_assoc] using hlater k (by omega)

/-- Kernel-checked digital conclusion for the five good-slope intervals,
including all errors tending to zero. Its hypotheses use the exact integer
numerators of the pulled-back exclusive domains, with denominator 486.
The analytic recurrence-to-inequality bridge is separate. -/
theorem good_slopes_eventually_periodic (r : ℝ) (hr : GoodSlope r)
    (digits : ℕ → Fin 4) (errors : ℕ → ℝ)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε)
    (approximate : ∀ n (j k : Fin 5),
      (discrepancy (wordWindow digits n).val j.val k.val).1 * r +
      (discrepancy (wordWindow digits n).val j.val k.val).2 ≤ errors n) :
    ∃ start, ∀ n ≥ start, digits (n+4) = digits n := by
  have transfer (edges : List ℕ) (rank : Fin 256 → ℕ) (next : Fin 256 → Fin 256)
      (rank_edges : ∀ v w : Fin 256,
        (4 * v.val + w.val % 4 ∈ edges ∧
          (4 * v.val + w.val % 4) % 256 = w.val) → rank v ≤ rank w)
      (same_rank_edges : ∀ v w : Fin 256,
        (4 * v.val + w.val % 4 ∈ edges ∧
          (4 * v.val + w.val % 4) % 256 = w.val) →
        rank v = rank w → w = next v)
      (next_four : ∀ v, next (next (next (next v))) = v)
      (check : ∀ e : Fin 1024, Feasible e.val r → e.val ∈ edges) :
      ∃ start, ∀ n ≥ start, digits (n+4) = digits n :=
    digits_periodic_of_eventually_retained edges rank next rank_edges
      same_rank_edges next_four digits
      (eventually_retained (fun e => e.val ∈ edges) r check
        (wordWindow digits) errors vanishing approximate)
  rcases hr with h | h | h | h | h
  · exact transfer Band0.edges Band0.rank Band0.next Band0.rank_edges
      Band0.same_rank_edges Band0.next_four
      (fun e => Band0.feasible_mem_edges e r h.1 h.2)
  · exact transfer Band1.edges Band1.rank Band1.next Band1.rank_edges
      Band1.same_rank_edges Band1.next_four
      (fun e => Band1.feasible_mem_edges e r h.1 h.2)
  · exact transfer Band2.edges Band2.rank Band2.next Band2.rank_edges
      Band2.same_rank_edges Band2.next_four
      (fun e => Band2.feasible_mem_edges e r h.1 h.2)
  · exact transfer Band3.edges Band3.rank Band3.next Band3.rank_edges
      Band3.same_rank_edges Band3.next_four
      (fun e => Band3.feasible_mem_edges e r h.1 h.2)
  · exact transfer Band4.edges Band4.rank Band4.next Band4.rank_edges
      Band4.same_rank_edges Band4.next_four
      (fun e => Band4.feasible_mem_edges e r h.1 h.2)

end LambdaCantor.Integer
