import LambdaCantor.Last.AdaptiveTree
import LambdaCantor.Last.CompactStrictReturns

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

/-- The normalized data carried along a return branch. -/
structure ReturnState (levels : Set ℝ) (bound : ℝ≥0) where
  level : ℝ
  level_mem : level ∈ levels
  error : (ℝ × ℝ) → ℝ
  error_zero : error 0 = 0
  error_lipschitz : LipschitzWith bound error

namespace ReturnState
variable {levels : Set ℝ} {bound : ℝ≥0}

def residual (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ) (state : ReturnState levels bound)
    (point : ℝ × ℝ) : ℝ := linear point + state.error point - state.level

def nextLevel (ratio : ℝ) (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (state : ReturnState levels bound) (word : List (Bool × Bool)) : ℝ :=
  returnLevel (ratio ^ word.length) state.level
    (linear (wordMap ratio word 0) + state.error (wordMap ratio word 0))

def next (ratio : ℝ) (hpositive : 0 < ratio) (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (state : ReturnState levels bound) (word : List (Bool × Bool))
    (returns : state.nextLevel ratio linear word ∈ levels) : ReturnState levels bound where
  level := state.nextLevel ratio linear word
  level_mem := returns
  error := normalizedError state.error (ratio ^ word.length) (wordMap ratio word 0)
  error_zero := normalizedError_zero _ _ _
  error_lipschitz := normalizedError_lipschitz state.error_lipschitz _ (pow_pos hpositive _) _

theorem next_residual (ratio : ℝ) (hpositive : 0 < ratio) (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (state : ReturnState levels bound) (word : List (Bool × Bool))
    (returns : state.nextLevel ratio linear word ∈ levels) (point : ℝ × ℝ) :
    state.residual linear (wordMap ratio word point) =
      ratio ^ word.length * (state.next ratio hpositive linear word returns).residual linear point := by
  have identity := restriction_identity linear state.error (ratio ^ word.length) state.level
    (ne_of_gt (pow_pos hpositive _)) (wordMap ratio word 0) point
  simpa only [residual, next, nextLevel, restrictPoint, ← wordMap_affine] using identity

theorem error_abs_le_on_dust (ratio : ℝ) (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (state : ReturnState levels bound) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    |state.error point| ≤ bound := by
  have hdist := state.error_lipschitz.dist_le_mul point 0
  rw [state.error_zero, Real.dist_eq, sub_zero] at hdist
  exact hdist.trans (mul_le_of_le_one_right bound.coe_nonneg
    (dust_dist_le_one hnonnegative hless hpoint
      ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩))

theorem residual_abs_le (ratio : ℝ) (hnonnegative : 0 ≤ ratio) (hless : ratio < 1)
    (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ) (linearBound levelBound : ℝ)
    (hlinear : ∀ point ∈ cantorDust ratio, |linear point| ≤ linearBound)
    (hlevels : ∀ level ∈ levels, |level| ≤ levelBound)
    (state : ReturnState levels bound) {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    |state.residual linear point| ≤ linearBound + bound + levelBound := by
  calc
    |state.residual linear point| ≤ |linear point + state.error point| + |state.level| :=
      abs_sub (linear point + state.error point) state.level
    _ ≤ (|linear point| + |state.error point|) + |state.level| :=
      add_le_add (abs_add_le (linear point) (state.error point)) (le_refl |state.level|)
    _ ≤ (linearBound + bound) + levelBound :=
      add_le_add (add_le_add (hlinear point hpoint)
        (state.error_abs_le_on_dust ratio hnonnegative hless hpoint))
        (hlevels state.level state.level_mem)

end ReturnState

/-- Assemble genuinely normalized states into the adaptive Cantor tree.
The return-membership field is discharged by the uniform-margin calculation. -/
def normalizedReturnSystem (ratio : ℝ) (hpositive : 0 < ratio)
    (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ) (levels : Set ℝ) (bound : ℝ≥0)
    (word : ReturnState levels bound → Bool → List (Bool × Bool))
    (maxDepth : ℕ) (hlength_pos : ∀ state bit, 0 < (word state bit).length)
    (hlength_le : ∀ state bit, (word state bit).length ≤ maxDepth)
    (returns : ∀ (state : ReturnState levels bound) (bit : Bool),
      state.nextLevel ratio linear (word state bit) ∈ levels) :
    AdaptiveWordSystem (ReturnState levels bound) where
  word := word
  next state bit := state.next ratio hpositive linear (word state bit) (returns state bit)
  maxDepth := maxDepth
  length_pos := hlength_pos
  length_le := hlength_le

end LambdaCantor.Last
