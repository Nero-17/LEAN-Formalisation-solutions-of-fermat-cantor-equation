import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

noncomputable section
open Filter Topology

namespace LambdaCantor.First.Roots

/-- Deletion cannot increase the upper envelope. Finite refinement is controlled
only by the positive replacement errors, exactly as in (root-one-sided). -/
theorem refinement_one_sided_finite (kernels deleted errors : ℕ → ℝ)
    (deleted_nonnegative : ∀ n, 0 ≤ deleted n)
    (refinement : ∀ n, kernels (n + 1) ≤ kernels n - deleted n + errors n) :
    ∀ n, kernels n ≤ kernels 0 + ∑ i ∈ Finset.range n, errors i := by
  intro n
  induction n with
  | zero => simp
  | succ n induction_hypothesis =>
    rw [Finset.sum_range_succ]
    calc
      kernels (n + 1) ≤ kernels n - deleted n + errors n := refinement n
      _ ≤ kernels n + errors n := by
        simpa only [add_comm] using!
          add_le_add_right (sub_le_self (kernels n) (deleted_nonnegative n)) (errors n)
      _ ≤ kernels 0 + (∑ i ∈ Finset.range n, errors i) + errors n :=
        by simpa only [add_comm] using! add_le_add_right induction_hypothesis (errors n)
      _ = _ := by ring

/-- The limiting upper envelope retains only positive errors. This estimate
does not pay the telescoping deleted mass a second time. -/
theorem refinement_one_sided_limit (kernels deleted errors : ℕ → ℝ) (limit : ℝ)
    (deleted_nonnegative : ∀ n, 0 ≤ deleted n)
    (refinement : ∀ n, kernels (n + 1) ≤ kernels n - deleted n + errors n)
    (errors_summable : Summable errors) (convergence : Tendsto kernels atTop (𝓝 limit)) :
    limit ≤ kernels 0 + ∑' n, errors n := by
  apply le_of_tendsto_of_tendsto convergence
    (tendsto_const_nhds.add errors_summable.hasSum.tendsto_sum_nat)
  exact Filter.Eventually.of_forall
    (refinement_one_sided_finite kernels deleted errors deleted_nonnegative refinement)

/-- Deleted mass in a decreasing sequence of finite-mass approximations is summable.
This is the telescoping step for the unions of cylinders meeting a compact address set. -/
theorem summable_deleted_mass (mass : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ mass n)
    (decreasing : Antitone mass) : Summable (fun n => mass n - mass (n + 1)) := by
  apply summable_of_sum_range_le (fun n => sub_nonneg.2 (decreasing (by omega)))
  intro n
  have telescopes : ∑ i ∈ Finset.range n, (mass i - mass (i + 1)) = mass 0 - mass n := by
    induction n with
    | zero => simp
    | succ n induction_hypothesis =>
      rw [Finset.sum_range_succ, induction_hypothesis]
      ring
  rw [telescopes]
  exact sub_le_self _ (nonnegative n)

/-- Abstract complete-space version of the kernel convergence step. Refinement
subtracts deleted kernels and adds replacement errors. Only the errors and deleted
norms need be summable; positivity is used to obtain the latter by mass telescoping. -/
theorem kernel_replacement_converges {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (kernels deleted replacements : ℕ → E) (mass errorBound : ℕ → ℝ)
    (mass_nonnegative : ∀ n, 0 ≤ mass n) (mass_decreasing : Antitone mass)
    (refinement : ∀ n, kernels (n + 1) = kernels n - deleted n + replacements n)
    (deleted_norm : ∀ n, ‖deleted n‖ ≤ mass n - mass (n + 1))
    (replacement_norm : ∀ n, ‖replacements n‖ ≤ errorBound n)
    (errors_summable : Summable errorBound) :
    ∃ limit, Tendsto kernels atTop (𝓝 limit) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_dist_le_of_summable
    (fun n => (mass n - mass (n + 1)) + errorBound n)
  · intro n
    rw [dist_comm, dist_eq_norm, refinement]
    have identity : kernels n - deleted n + replacements n - kernels n =
        -deleted n + replacements n := by abel
    rw [identity]
    calc
      ‖-deleted n + replacements n‖ ≤ ‖-deleted n‖ + ‖replacements n‖ := norm_add_le _ _
      _ ≤ (mass n - mass (n + 1)) + errorBound n := by
        rw [norm_neg]
        exact add_le_add (deleted_norm n) (replacement_norm n)
  · exact (summable_deleted_mass mass mass_nonnegative mass_decreasing).add errors_summable

end LambdaCantor.First.Roots
