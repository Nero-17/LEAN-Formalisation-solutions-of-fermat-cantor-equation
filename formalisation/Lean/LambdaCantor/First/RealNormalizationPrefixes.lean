import LambdaCantor.First.RootFibreInterface
import LambdaCantor.First.CylinderCalculus
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First.Roots

def realRootLeftPrefix (depth : ℕ) (index : ℕ) : Bool := decide (index = depth)
def realRootRightPrefix (depth : ℕ) (index : ℕ) : Bool := decide (index < depth)

theorem realRootLeftPrefix_coordinate (ratio : ℝ) (depth padding : ℕ) (hpadding : 1 ≤ padding)
    (digits : ℕ → Bool) :
    cylinderCoordinate (realRootLeftPrefix depth) (depth + padding) digits ratio =
      firstRootX depth padding digits ratio := by
  have hprefix : prefixValue ratio (realRootLeftPrefix depth) (depth + padding) =
      (1 - ratio) * ratio ^ depth := by
    simp [prefixValue, realRootLeftPrefix, show depth < depth + padding by omega]
  rw [cylinderCoordinate, hprefix, firstRootX, pow_add]
  ring

theorem realRootRightPrefix_coordinate (ratio : ℝ) (depth padding : ℕ) (digits : ℕ → Bool) :
    cylinderCoordinate (realRootRightPrefix depth) (depth + padding) digits ratio =
      firstRootY depth padding digits ratio := by
  have hsum : (∑ index ∈ Finset.range (depth + padding),
      (if decide (index < depth) then (1 : ℝ) else 0) * ratio ^ index) =
      ∑ index ∈ Finset.range depth, ratio ^ index := by
    calc
      _ = ∑ index ∈ Finset.range depth,
          (if decide (index < depth) then (1 : ℝ) else 0) * ratio ^ index := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.le_add_right _ _))
        intro index hindex hout
        simp only [Finset.mem_range] at hout
        simp [hout]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index hindex
        simp [Finset.mem_range.mp hindex]
  have hprefix : prefixValue ratio (realRootRightPrefix depth) (depth + padding) =
      1 - ratio ^ depth := by
    unfold prefixValue realRootRightPrefix
    rw [hsum, mul_comm]
    exact geom_sum_mul_neg ratio depth
  rw [cylinderCoordinate, hprefix]
  rfl

theorem realRootPrefix_residual (exponent ratio : ℝ) (leftDepth rightDepth padding : ℕ)
    (hpadding : 1 ≤ padding) (digits : ℕ → Bool × Bool) :
    cylinderResidual exponent (realRootLeftPrefix leftDepth) (realRootRightPrefix rightDepth)
      (leftDepth + padding) (rightDepth + padding) digits ratio =
    firstRootResidual exponent leftDepth rightDepth padding
      (fun index => (digits index).1) (fun index => (digits index).2) ratio := by
  rw [cylinderResidual, realRootLeftPrefix_coordinate _ _ _ hpadding,
    realRootRightPrefix_coordinate]
  rfl

end LambdaCantor.First.Roots

