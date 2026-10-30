import LambdaCantor.Last.ReturnAtlas
import LambdaCantor.Last.BinaryDimension

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last
namespace FiniteReturnAtlas
variable {ratio : ℝ} {linear : (ℝ × ℝ) →ₗ[ℝ] ℝ} {levels : Set ℝ}

theorem system_siblings (atlas : FiniteReturnAtlas ratio linear levels)
    (hpositive : 0 < ratio) (hless : ratio < 1 / 2) (bound : ℝ≥0)
    (hsmall : (bound : ℝ) < atlas.margin * ratio ^ atlas.maxDepth)
    (state : ReturnState levels bound) (firstBit secondBit : Bool) (different : firstBit ≠ secondBit)
    {first second : ℝ × ℝ} (hfirst : first ∈ cantorDust ratio) (hsecond : second ∈ cantorDust ratio) :
    (1 - 2 * ratio) * ratio ^ atlas.maxDepth ≤
      dist (wordMap ratio ((atlas.system hpositive (by linarith) bound hsmall).word state firstBit) first)
        (wordMap ratio ((atlas.system hpositive (by linarith) bound hsmall).word state secondBit) second) := by
  cases firstBit <;> cases secondBit
  · exact False.elim (different rfl)
  · exact diverging_words_distance_gap hpositive hless _ _
      (atlas.pair ⟨state.level, state.level_mem⟩).diverge atlas.maxDepth
      (atlas.length_le _ false) hfirst hsecond
  · rw [dist_comm]
    exact diverging_words_distance_gap hpositive hless _ _
      (atlas.pair ⟨state.level, state.level_mem⟩).diverge atlas.maxDepth
      (atlas.length_le _ false) hsecond hfirst
  · exact False.elim (different rfl)

/-- Core strict-return conclusion, for initial levels in the compact returning set.
All tree construction, limit membership and positive dimension are proved internally. -/
theorem positive_dimension (atlas : FiniteReturnAtlas ratio linear levels)
    (hpositive : 0 < ratio) (hless : ratio < 1 / 2) (bound : ℝ≥0)
    (hsmall : (bound : ℝ) < atlas.margin * ratio ^ atlas.maxDepth)
    (linearBound levelBound : ℝ) (hlinearBound : 0 ≤ linearBound) (hlevelBound : 0 ≤ levelBound)
    (hlinear : ∀ point ∈ cantorDust ratio, |linear point| ≤ linearBound)
    (hlevels : ∀ level ∈ levels, |level| ≤ levelBound)
    (initial : ReturnState levels bound) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      linear point + initial.error point = initial.level} := by
  have hless_one : ratio < 1 := by linarith
  let system := atlas.system hpositive hless_one bound hsmall
  let tree := system.compactTree ratio hpositive hless_one initial
  have hmaxDepth : 0 < atlas.maxDepth :=
    ((atlas.pair ⟨initial.level, initial.level_mem⟩).length_pos false).trans_le
      (atlas.length_le _ false)
  have hpow_lt : ratio ^ atlas.maxDepth < 1 := pow_lt_one₀ hpositive.le hless_one hmaxDepth.ne'
  have hsep_pos : 0 < (1 - 2 * ratio) * ratio ^ atlas.maxDepth :=
    mul_pos (by linarith) (pow_pos hpositive _)
  have hdimension : 0 < dimH (Set.range tree.coding) := by
    apply positive_dimension_of_separated_binary_coding tree.coding tree.continuous_coding.measurable
      (ratio ^ atlas.maxDepth) ((1 - 2 * ratio) * ratio ^ atlas.maxDepth)
      (pow_pos hpositive _) hpow_lt hsep_pos
    · intro depth first second different
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      have hsep := system.coding_separation ratio hpositive hless_one
        ((1 - 2 * ratio) * ratio ^ atlas.maxDepth) hsep_pos.le
        (fun state firstBit secondBit different first hfirst second hsecond =>
          atlas.system_siblings hpositive hless bound hsmall state firstBit secondBit different hfirst hsecond)
        initial depth first second different
      change ((1 - 2 * ratio) * ratio ^ atlas.maxDepth) *
        ratio ^ (depth * atlas.maxDepth) ≤ dist (tree.coding first) (tree.coding second) at hsep
      rw [Nat.mul_comm depth atlas.maxDepth, pow_mul] at hsep
      exact hsep
    · exact (isCompact_range tree.continuous_coding).measurableSet
    · intro branch
      exact Set.mem_range_self branch
  apply hdimension.trans_le (dimH_mono ?_)
  rintro point ⟨branch, rfl⟩
  refine ⟨system.coding_mem_dust ratio hpositive hless_one initial branch, ?_⟩
  have hzero := system.coding_residual_zero ratio hpositive hless_one
    (ReturnState.residual linear)
    (fun state bit point => state.next_residual ratio hpositive linear _ _ point)
    (linearBound + bound + levelBound) (by positivity)
    (fun state point hpoint => state.residual_abs_le ratio hpositive.le hless_one linear
      linearBound levelBound hlinear hlevels hpoint) initial branch
  exact sub_eq_zero.mp hzero

end FiniteReturnAtlas
end LambdaCantor.Last
