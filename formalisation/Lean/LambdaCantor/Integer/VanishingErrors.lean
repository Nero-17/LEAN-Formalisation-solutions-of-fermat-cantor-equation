import Mathlib.Data.Fintype.Fin
import LambdaCantor.Integer.Feasibility
import Mathlib.Data.Finset.Lattice.Fold
namespace LambdaCantor.Integer
/-- Finite closed constraints persist under vanishing errors: every symbol
which violates a limiting constraint disappears after a finite time. -/
theorem eventually_good_of_vanishing_errors {Symbol Constraint : Type*}
    [Fintype Symbol] (good : Symbol → Prop) (value : Symbol → Constraint → ℝ)
    (exclusion : ∀ s, ¬ good s → ∃ c, 0 < value s c)
    (symbols : ℕ → Symbol) (errors : ℕ → ℝ)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε)
    (approximate : ∀ n c, value (symbols n) c ≤ errors n) :
    ∃ start, ∀ n ≥ start, good (symbols n) := by
  classical
  have eliminate : ∀ s, ∃ start, ∀ n ≥ start, symbols n = s → good s := by
    intro s
    by_cases hs : good s
    · exact ⟨0, fun _ _ _ => hs⟩
    · obtain ⟨c, hc⟩ := exclusion s hs
      obtain ⟨start, hstart⟩ := vanishing (value s c) hc
      refine ⟨start, ?_⟩
      intro n hn heq
      have hvalue := approximate n c
      rw [heq] at hvalue
      exact False.elim ((not_lt_of_ge hvalue) (hstart n hn))
  choose threshold hthreshold using eliminate
  refine ⟨Finset.univ.sup threshold, ?_⟩
  intro n hn
  apply hthreshold (symbols n) n _ rfl
  exact le_trans (Finset.le_sup (Finset.mem_univ (symbols n))) hn

/-- This specializes the finite stability principle to the paper's five-letter
exclusive-domain inequalities. The exact feasible-word theorem is a parameter,
so no computational conclusion is assumed here. -/
theorem eventually_retained (retained : Fin 1024 → Prop) (r : ℝ)
    (check : ∀ e, Feasible e.val r → retained e)
    (words : ℕ → Fin 1024) (errors : ℕ → ℝ)
    (vanishing : ∀ ε > 0, ∃ start, ∀ n ≥ start, errors n < ε)
    (approximate : ∀ n (j k : Fin 5),
      (discrepancy (words n).val j.val k.val).1 * r +
      (discrepancy (words n).val j.val k.val).2 ≤ errors n) :
    ∃ start, ∀ n ≥ start, retained (words n) := by
  apply eventually_good_of_vanishing_errors retained
    (fun e (c : Fin 5 × Fin 5) =>
      (discrepancy e.val c.1.val c.2.val).1 * r +
      (discrepancy e.val c.1.val c.2.val).2)
    _ words errors vanishing (fun n c => approximate n c.1 c.2)
  intro e he
  have infeasible : ¬ Feasible e.val r := fun hf => he (check e hf)
  simp only [Feasible, not_forall, not_le] at infeasible
  obtain ⟨j, k, h⟩ := infeasible
  exact ⟨(j,k), h⟩
end LambdaCantor.Integer

