import LambdaCantor.First.RootFibreInterface
import LambdaCantor.AE.CenteredCylinders
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
open scoped BigOperators

namespace LambdaCantor.AE
open First.Roots

def centeredLeftPrefix (horizontalDepth : ℕ) (index : ℕ) : Bool := decide (horizontalDepth ≤ index)

def centeredRightPrefix (verticalDepth : ℕ) (index : ℕ) : Bool := decide (index < verticalDepth)

theorem centeredLeftPrefix_value (ratio : ℝ) (horizontalDepth tailDepth : ℕ) :
    prefixValue ratio (centeredLeftPrefix horizontalDepth) (horizontalDepth + tailDepth) =
      ratio^horizontalDepth * (1-ratio^tailDepth) := by
  induction tailDepth with
  | zero =>
    have zero_sum : (∑ index ∈ Finset.range horizontalDepth,
        (if centeredLeftPrefix horizontalDepth index then (1 : ℝ) else 0)*ratio^index) = 0 := by
      apply Finset.sum_eq_zero
      intro index membership
      simp [centeredLeftPrefix, not_le_of_gt (Finset.mem_range.mp membership)]
    unfold prefixValue
    rw [Nat.add_zero, zero_sum]
    simp
  | succ tailDepth induction_hypothesis =>
    have new_digit : centeredLeftPrefix horizontalDepth (horizontalDepth+tailDepth) = true := by
      simp [centeredLeftPrefix]
    unfold prefixValue at induction_hypothesis ⊢
    rw [show horizontalDepth + Nat.succ tailDepth = (horizontalDepth+tailDepth)+1 by omega,
      Finset.sum_range_succ, mul_add, induction_hypothesis]
    rw [new_digit]
    simp only [if_true, one_mul, pow_succ, pow_add]
    ring

theorem centeredRightPrefix_value (ratio : ℝ) (verticalDepth tailDepth : ℕ) :
    prefixValue ratio (centeredRightPrefix verticalDepth) (verticalDepth + tailDepth) =
      1-ratio^verticalDepth := by
  have sum_identity : (∑ index ∈ Finset.range (verticalDepth+tailDepth),
      (if centeredRightPrefix verticalDepth index then (1 : ℝ) else 0)*ratio^index) =
      ∑ index ∈ Finset.range verticalDepth, ratio^index := by
    calc
      _ = ∑ index ∈ Finset.range verticalDepth,
          (if centeredRightPrefix verticalDepth index then (1 : ℝ) else 0)*ratio^index := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.le_add_right _ _))
        intro index _ outside
        simp only [Finset.mem_range] at outside
        simp [centeredRightPrefix, outside]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro index membership
        simp [centeredRightPrefix, Finset.mem_range.mp membership]
  unfold prefixValue
  rw [sum_identity, mul_comm]
  exact geom_sum_mul_neg ratio verticalDepth

theorem centered_prefix_coordinates (ratio : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (first second : ℕ → Bool) :
    (cylinderCoordinate (centeredLeftPrefix horizontalDepth) (horizontalDepth+tailDepth) first ratio,
      cylinderCoordinate (centeredRightPrefix verticalDepth) (verticalDepth+tailDepth) second ratio) =
      centeredCylinder ratio horizontalDepth verticalDepth tailDepth
        (address ratio first, address ratio second) := by
  rw [cylinderCoordinate, cylinderCoordinate, centeredLeftPrefix_value, centeredRightPrefix_value]
  ext <;> simp only [centeredCylinder, Prod.fst, Prod.snd, pow_add] <;> ring

end LambdaCantor.AE
