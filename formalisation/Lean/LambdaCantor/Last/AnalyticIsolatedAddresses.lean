import LambdaCantor.Last.AnalyticIsolatedAddressCore
import LambdaCantor.Last.AnalyticIsolatedBoundaryShadow

noncomputable section
namespace LambdaCantor.Last
theorem pairedAddressTail_boundary_orbit {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1) (digits : ℕ → Bool × Bool) (depth : ℕ) :
    (pairedAddressTail ratio digits depth).1+(1+ratio)*(pairedAddressTail ratio digits depth).2 =
      boundaryChildOffset ratio (digits depth)+ratio*
        ((pairedAddressTail ratio digits (depth+1)).1+
          (1+ratio)*(pairedAddressTail ratio digits (depth+1)).2) := by
  rw [pairedAddressTail_recurrence nonnegative less_one digits depth]
  simp only [wordMap, wordMap_nil, boundaryChildOffset, digitPoint,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

end LambdaCantor.Last

