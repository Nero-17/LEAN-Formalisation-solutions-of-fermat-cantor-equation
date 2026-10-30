import LambdaCantor.AE.NewtonRefinement
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

theorem FrozenNewtonKernel.law_exact_digit_split (kernel : FrozenNewtonKernel)
    (ratio_nonnegative : 0 ≤ kernel.freezing) (ratio_less_one : kernel.freezing < 1) :
    kernel.law = ∑ digit : Bool × Bool, (4 : ℝ≥0∞)⁻¹ • (kernel.child digit).law := by
  rw [kernel.law_exact_child_split ratio_nonnegative ratio_less_one]
  exact (Equiv.funUnique (Fin 1) (Bool × Bool)).sum_comp
    (fun digit => (4 : ℝ≥0∞)⁻¹ • (kernel.child digit).law)

/-- The old depth mixture splits exactly into the four affine children of
each actual kernel, now indexed by the genuine next-level paired words. -/
theorem newton_mixture_exact_prefix_refinement (depth : ℕ)
    (kernels : (Fin depth → Bool × Bool) → FrozenNewtonKernel)
    (ratios_nonnegative : ∀ word, 0 ≤ (kernels word).freezing)
    (ratios_less_one : ∀ word, (kernels word).freezing < 1) :
    (∑ word : Fin depth → Bool × Bool, ((4 : ℝ≥0∞)⁻¹^depth) • (kernels word).law) =
      ∑ word : Fin (depth+1) → Bool × Bool, ((4 : ℝ≥0∞)⁻¹^(depth+1)) •
        ((kernels (fun index => word index.castSucc)).child (word (Fin.last depth))).law := by
  calc
    _ = ∑ word : Fin depth → Bool × Bool, ∑ digit : Bool × Bool,
        ((4 : ℝ≥0∞)⁻¹^(depth+1)) • ((kernels word).child digit).law := by
      apply Finset.sum_congr rfl
      intro word _
      rw [(kernels word).law_exact_digit_split (ratios_nonnegative word) (ratios_less_one word), Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro digit _
      rw [smul_smul, pow_succ]
    _ = ∑ digit : Bool × Bool, ∑ word : Fin depth → Bool × Bool,
        ((4 : ℝ≥0∞)⁻¹^(depth+1)) • ((kernels word).child digit).law := Finset.sum_comm
    _ = _ := by
      rw [← (Fin.snocEquiv (fun _ : Fin (depth+1) => Bool × Bool)).sum_comp
        (fun word : Fin (depth+1) → Bool × Bool => ((4 : ℝ≥0∞)⁻¹^(depth+1)) •
          ((kernels (fun index => word index.castSucc)).child (word (Fin.last depth))).law)]
      conv_rhs => rw [Fintype.sum_prod_type]
      simp only [Fin.snocEquiv_apply, Fin.snoc_castSucc, Fin.snoc_last]

end LambdaCantor.AE
