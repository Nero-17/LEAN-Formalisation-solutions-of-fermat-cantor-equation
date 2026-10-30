import LambdaCantor.RationalPowers.SharedLogGeometry
import LambdaCantor.Integer.GoodSlopes
import Mathlib.Tactic.FinCases

namespace LambdaCantor.RationalPowers
open Integer

/-- Each of the twelve decoded bands is analytically in a proved direct
GoodSlope band or the reciprocal of one. Combined with each row's separate
GeometryChecked predicate, this certifies its entire derivative interval. -/
theorem sharedSlopeBand_orientations (band : Fin 12) :
    (band.val < 6 ∧ 1 < ((sharedSlopeBand band.val).lower : ℝ) ∧
      ((sharedSlopeBand band.val).upper : ℝ) < 3 ∧
      ∀ slope : ℝ, ((sharedSlopeBand band.val).lower : ℝ) < slope →
        slope < ((sharedSlopeBand band.val).upper : ℝ) → GoodSlope slope) ∨
    (6 ≤ band.val ∧ 1/3 < ((sharedSlopeBand band.val).lower : ℝ) ∧
      ((sharedSlopeBand band.val).upper : ℝ) < 1 ∧
      ∀ slope : ℝ, 1/((sharedSlopeBand band.val).upper : ℝ) < slope →
        slope < 1/((sharedSlopeBand band.val).lower : ℝ) → GoodSlope slope) := by
  fin_cases band
  · refine Or.inl ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inl ⟨by linarith,by linarith⟩
  · refine Or.inl ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inl ⟨by linarith,by linarith⟩
  · refine Or.inl ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)
  · refine Or.inl ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩))
  · refine Or.inl ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩)))
  · refine Or.inl ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith,by linarith⟩)))
  · refine Or.inr ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inl ⟨by linarith,by linarith⟩
  · refine Or.inr ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inl ⟨by linarith,by linarith⟩
  · refine Or.inr ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)
  · refine Or.inr ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩))
  · refine Or.inr ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith,by linarith⟩)))
  · refine Or.inr ⟨by decide, by norm_num [sharedSlopeBand, SharedSlopeBand.lower],
      by norm_num [sharedSlopeBand, SharedSlopeBand.upper], ?_⟩
    intro slope lower upper
    norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper] at lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by linarith,by linarith⟩)))

theorem sharedSlopeBand_positive (band : Fin 12) :
    (0 : ℝ) < (sharedSlopeBand band.val).lower ∧
      (0 : ℝ) < (sharedSlopeBand band.val).upper := by
  fin_cases band <;> norm_num [sharedSlopeBand, SharedSlopeBand.lower, SharedSlopeBand.upper]

end LambdaCantor.RationalPowers
