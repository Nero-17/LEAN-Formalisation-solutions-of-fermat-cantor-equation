import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators

namespace LambdaCantor.AE

theorem paired_word_snoc_sum (depth : ℕ) (function : (Fin (depth+1) → Bool × Bool) → ℝ) :
    (∑ word : Fin (depth+1) → Bool × Bool, function word) =
      ∑ digit : Bool × Bool, ∑ word : Fin depth → Bool × Bool, function (Fin.snoc word digit) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (depth+1) => Bool × Bool)).sum_comp function,
    Fintype.sum_prod_type]
  rfl

/-- Refining the Bernoulli prefix repeats the old energy exactly four times
and divides its weight by four. There is no extra branching factor. -/
theorem paired_parent_energy_refinement (depth : ℕ) (energy : (Fin depth → Bool × Bool) → ℝ) :
    (∑ child : Fin (depth+1) → Bool × Bool,
      (1/4 : ℝ)^(depth+1)*energy (fun index => child index.castSucc)) =
      ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*energy word := by
  rw [paired_word_snoc_sum]
  simp only [Fin.snoc_castSucc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
  change (4 : ℝ)*(∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^(depth+1)*energy word) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [pow_succ]
  ring

theorem paired_adjacent_energy_sum (depth : ℕ)
    (parentEnergy : (Fin depth → Bool × Bool) → ℝ)
    (childEnergy : (Fin (depth+1) → Bool × Bool) → ℝ) :
    (∑ child : Fin (depth+1) → Bool × Bool, (1/4 : ℝ)^(depth+1)*
      (parentEnergy (fun index => child index.castSucc)+childEnergy child)) =
      (∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*parentEnergy word) +
        ∑ child : Fin (depth+1) → Bool × Bool, (1/4 : ℝ)^(depth+1)*childEnergy child := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [paired_parent_energy_refinement]

end LambdaCantor.AE
