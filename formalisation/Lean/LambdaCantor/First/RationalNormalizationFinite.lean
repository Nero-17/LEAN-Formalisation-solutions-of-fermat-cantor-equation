import LambdaCantor.First.RationalNormalizationConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First

/-- Finite sums preserve uniform convergence to zero. -/
theorem tendstoUniformly_finset_sum_zero {ι α : Type*} (indices : Finset ι)
    (functions : ι → ℕ → α → ℝ)
    (hfunctions : ∀ term ∈ indices, TendstoUniformly (functions term)
      (fun _ => (0 : ℝ)) Filter.atTop) :
    TendstoUniformly (fun index point => ∑ term ∈ indices, functions term index point)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
          Filter.atTop (nhds 0)).tendstoUniformly_const (α := α)
  | @insert term indices hnotmem ih =>
      have hterm := hfunctions term (Finset.mem_insert_self _ _)
      have hsum := ih (fun j hj => hfunctions j (Finset.mem_insert_of_mem hj))
      have hadd := hterm.add hsum
      have hsource :
          (functions term + fun index point => ∑ term ∈ indices, functions term index point) =
            (fun index point => ∑ term ∈ insert term indices, functions term index point) := by
        funext index point
        simp only [Pi.add_apply, Finset.sum_insert hnotmem]
      have hzero : ((fun _ : α => (0 : ℝ)) + fun _ : α => (0 : ℝ)) =
          (fun _ : α => (0 : ℝ)) := by
        funext point
        simp only [Pi.add_apply, zero_add]
      rw [hsource, hzero] at hadd
      exact hadd

/-- Natural scalar coefficients preserve uniform convergence to zero. -/
theorem tendstoUniformly_nat_mul_zero {α : Type*} (functions : ℕ → α → ℝ)
    (hfunctions : TendstoUniformly functions (fun _ => (0 : ℝ)) Filter.atTop)
    (coefficient : ℕ) :
    TendstoUniformly (fun index point => (coefficient : ℝ) * functions index point)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  induction coefficient with
  | zero =>
      simpa only [Nat.cast_zero, zero_mul] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
          Filter.atTop (nhds 0)).tendstoUniformly_const (α := α)
  | succ coefficient ih =>
      have hadd := ih.add hfunctions
      have hsource :
          ((fun index point => (coefficient : ℝ) * functions index point) + functions) =
            (fun index point => ((coefficient + 1 : ℕ) : ℝ) * functions index point) := by
        funext index point
        simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      have hzero : ((fun _ : α => (0 : ℝ)) + fun _ : α => (0 : ℝ)) =
          (fun _ : α => (0 : ℝ)) := by
        funext point
        simp only [Pi.add_apply, zero_add]
      rw [hsource, hzero] at hadd
      exact hadd

/-- The entire finite binomial remainder converges uniformly to zero. -/
theorem tendstoUniformly_powersFour_binomial_remainder {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper)
    (exponent : ℕ) (depth : ℕ → ℕ → ℕ) (padding : ℕ → ℕ)
    (hdepth : ∀ term ∈ Finset.range (exponent - 1),
      Filter.Tendsto (depth term) Filter.atTop Filter.atTop) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        ∑ term ∈ Finset.range (exponent - 1),
          (exponent.choose (term + 2) : ℝ) *
            ((point.1 : ℝ) ^ depth term index *
              (-powersFourRightFactor (padding index) point.2 point.1) ^ (term + 2)))
      (fun _ => (0 : ℝ)) Filter.atTop := by
  apply tendstoUniformly_finset_sum_zero
  intro term hterm
  exact tendstoUniformly_nat_mul_zero _
    (tendstoUniformly_powersFour_remainder_term hlower hupper hordered
      (depth term) padding (hdepth term hterm) (term + 2)) _

/-- The finite binomial remainder also vanishes after parameter differentiation. -/
theorem tendstoUniformly_powersFour_binomial_remainder_derivative {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper)
    (exponent : ℕ) (depth : ℕ → ℕ → ℕ) (padding : ℕ → ℕ)
    (hdepth : ∀ term ∈ Finset.range (exponent - 1),
      Filter.Tendsto (depth term) Filter.atTop Filter.atTop)
    (hpadding : Filter.Tendsto padding Filter.atTop Filter.atTop) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter => ∑ term ∈ Finset.range (exponent - 1),
          (exponent.choose (term + 2) : ℝ) *
            (parameter ^ depth term index *
              (-powersFourRightFactor (padding index) point.2 parameter) ^ (term + 2))) point.1)
      (fun _ => (0 : ℝ)) Filter.atTop := by
  have hsum := tendstoUniformly_finset_sum_zero (Finset.range (exponent - 1))
    (fun term index (point : Set.Icc lower upper × (ℕ → Bool)) =>
      (exponent.choose (term + 2) : ℝ) * deriv
        (fun parameter => parameter ^ depth term index *
          (-powersFourRightFactor (padding index) point.2 parameter) ^ (term + 2)) point.1)
    (fun term hterm => tendstoUniformly_nat_mul_zero _
      (tendstoUniformly_powersFour_remainder_term_derivative hlower hupper hordered
        (depth term) padding (hdepth term hterm) hpadding (term + 2)) _)
  convert hsum using 1
  funext index point
  have hpos : 0 < (point.1 : ℝ) := hlower.trans_le point.1.property.1
  have hlt := point.1.property.2.trans_lt hupper
  have hdiff (term : ℕ) : DifferentiableAt ℝ
      (fun parameter => parameter ^ depth term index *
        (-powersFourRightFactor (padding index) point.2 parameter) ^ (term + 2))
      (point.1 : ℝ) :=
    (((hasDerivAt_id (point.1 : ℝ)).pow (depth term index)).mul
      (((hasDerivAt_powersFourRightFactor hpos hlt (padding index) point.2).neg).pow
        (term + 2))).differentiableAt
  rw [deriv_fun_sum (fun term _ => (hdiff term).const_mul _)]
  apply Finset.sum_congr rfl
  intro term hterm
  exact deriv_const_mul _ (hdiff term)

end LambdaCantor.First


