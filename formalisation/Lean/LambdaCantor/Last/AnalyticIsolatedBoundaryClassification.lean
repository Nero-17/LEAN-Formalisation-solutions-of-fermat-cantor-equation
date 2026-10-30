import LambdaCantor.Last.AnalyticIsolatedBoundaryFinite
import Mathlib.Tactic.Push

noncomputable section
namespace LambdaCantor.Last

/-- Critical-phase address arithmetic after the genuine geometric shadowing
estimate. The two cases are proved separately: finitely many mixed symbols
give eventual periodicity; unbounded mixed symbols give stammering blocks.
No assumption of field membership, periodicity, or stammering is hidden here. -/
theorem boundary_exclusive_orbit_coordinates_in_field {ratio coefficient : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2) (coefficient_positive : 0 < coefficient)
    (orbit : ℕ → ℝ) (digits : ℕ → Bool × Bool) (errors : ℕ → ℝ)
    (recurrence : ∀ depth, orbit depth = boundaryChildOffset ratio (digits depth)+ratio*orbit (depth+1))
    (exclusive : ∀ depth, BoundaryApproxExclusive ratio (orbit depth) (errors depth) (digits depth))
    (error_bound : ∀ depth, errors depth ≤ coefficient*ratio^depth)
    (first_algebraic : IsAlgebraic ℚ (address ratio (fun index => (digits index).1)))
    (second_algebraic : IsAlgebraic ℚ (address ratio (fun index => (digits index).2))) :
    address ratio (fun index => (digits index).1) ∈ parameterField ratio ∧
      address ratio (fun index => (digits index).2) ∈ parameterField ratio := by
  classical
  by_cases mixed_unbounded : ∀ threshold : ℕ, ∃ depth : ℕ, threshold ≤ depth ∧
      (digits depth = (true,false) ∨ digits depth = (false,true))
  · obtain ⟨fixedLoss, blocks⟩ := boundary_shadowing_long_blocks critical coefficient_positive
      orbit digits errors recurrence exclusive error_bound mixed_unbounded
    constructor
    · apply boundary_algebraic_address_mem_parameterField critical _ first_algebraic fixedLoss
      intro threshold
      obtain ⟨start, start_lower, first_block, _⟩ := blocks threshold
      exact ⟨start, start_lower, first_block⟩
    · apply boundary_algebraic_address_mem_parameterField critical _ second_algebraic fixedLoss
      intro threshold
      obtain ⟨start, start_lower, _, second_block⟩ := blocks threshold
      exact ⟨start, start_lower, second_block⟩
  · push_neg at mixed_unbounded
    have mixed_finite : ∃ cutoff : ℕ, ∀ depth, cutoff ≤ depth →
        digits depth ≠ (true,false) ∧ digits depth ≠ (false,true) := by
      obtain ⟨cutoff, no_mixed⟩ := mixed_unbounded
      refine ⟨cutoff, ?_⟩
      intro depth depth_lower
      exact no_mixed depth depth_lower
    have periodic := boundary_finitely_mixed_periodic critical coefficient_positive
      orbit digits errors recurrence exclusive error_bound mixed_finite
    have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
    have positive : 0 ≤ ratio := by rw [critical]; nlinarith
    have less_one : ratio < 1 := by rw [critical]; nlinarith
    exact paired_periodic_coordinates_in_parameterField positive less_one periodic

end LambdaCantor.Last
