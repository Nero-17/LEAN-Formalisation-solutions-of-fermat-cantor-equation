import LambdaCantor.Certificates.IntegerFeasibility0
import LambdaCantor.Integer.Windows
import LambdaCantor.Integer.VanishingErrors

namespace LambdaCantor.Integer

/-- First-band conclusion, isolated so that the original periodicity lemma
does not depend on the other four finite certificates. -/
theorem band0_eventually_periodic (r : ℝ)
    (lower : (89 : ℝ)/73 < r) (upper : r < (171 : ℝ)/137)
    (digits : ℕ → Fin 4) (errors : ℕ → ℝ)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε)
    (approximate : ∀ n (j k : Fin 5),
      (discrepancy (wordWindow digits n).val j.val k.val).1 * r +
      (discrepancy (wordWindow digits n).val j.val k.val).2 ≤ errors n) :
    ∃ start, ∀ n ≥ start, digits (n+4) = digits n := by
  obtain ⟨start, retained⟩ := eventually_retained
    (fun e : Fin 1024 => e.val ∈ Band0.edges) r
    (fun e => Band0.feasible_mem_edges e r lower upper)
    (wordWindow digits) errors vanishing approximate
  obtain ⟨later, hlater⟩ := Band0.eventually_period_four
    (fun n => vertexWindow digits (start+n)) (by
      intro n
      simpa only [Band0.edge, Nat.add_assoc] using
        window_edge Band0.edges digits (start+n) (retained (start+n) (by omega)))
  refine ⟨start+later, digits_periodic_of_vertices digits (start+later) ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show start ≤ n by omega)
  simpa only [Nat.add_assoc] using hlater k (by omega)

/-- The original slope interval is strictly contained in the first certified band. -/
theorem original_band_eventually_periodic (r : ℝ)
    (lower : (11 : ℝ)/9 < r) (upper : r < (2027 : ℝ)/1624)
    (digits : ℕ → Fin 4) (errors : ℕ → ℝ)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε)
    (approximate : ∀ n (j k : Fin 5),
      (discrepancy (wordWindow digits n).val j.val k.val).1 * r +
      (discrepancy (wordWindow digits n).val j.val k.val).2 ≤ errors n) :
    ∃ start, ∀ n ≥ start, digits (n+4) = digits n :=
  band0_eventually_periodic r (by linarith) (by linarith)
    digits errors vanishing approximate

end LambdaCantor.Integer
