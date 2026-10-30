import LambdaCantor.First.CountNormalization
import LambdaCantor.First.TreeCover
import LambdaCantor.First.ProjectionThreshold

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory
open scoped ENNReal NNReal

def blockDepth (block : ℕ) : ℕ → ℕ
  | 0 => 0
  | level + 1 => blockDepth block level + block

theorem blockDepth_eq_mul (block level : ℕ) : blockDepth block level = block * level := by
  induction level with
  | zero => simp [blockDepth]
  | succ level hinduction => simp [blockDepth, hinduction, Nat.mul_succ]

theorem dimH_le_of_flat_target {ratio slope constant projectionExponent : ℝ}
    (hratio : 0 < ratio) (hcontract : ratio < 1) (hconstant : 0 ≤ constant)
    (hball : ∀ center radius : ℝ, 0 < radius →
      projectedMeasure ratio slope (Metric.ball center radius) ≤
        ENNReal.ofReal (constant * radius ^ projectionExponent))
    (block : ℕ) (hblock : 0 < block) (targetExponent : ℝ≥0)
    (hcost : (Nat.ceil (constant * (|slope| + 3) ^ projectionExponent *
      (4 * ratio ^ projectionExponent) ^ block) : ℝ) *
        (ratio ^ (targetExponent : ℝ)) ^ block < 1)
    (target : Set (ℝ × ℝ))
    (hsubset : target ⊆ (cantorSet ratio).prod (cantorSet ratio))
    (hflat : ∀ left ∈ target, ∀ right ∈ target,
      |(left.2 - right.2) - slope * (left.1 - right.1)| ≤
        ratio ^ block * |left.1 - right.1|) : dimH target ≤ targetExponent := by
  classical
  have hsmall : ENNReal.ofReal ratio ^ block < 1 := by
    rw [← ENNReal.ofReal_pow hratio.le]
    exact ENNReal.ofReal_lt_one.2 (pow_lt_one₀ hratio.le hcontract (Nat.ne_of_gt hblock))
  have hcostENN :
      (Nat.ceil (constant * (|slope| + 3) ^ projectionExponent *
        (4 * ratio ^ projectionExponent) ^ block) : ℝ≥0∞) *
        (ENNReal.ofReal ratio ^ block) ^ (targetExponent : ℝ) < 1 := by
    have hpower : (ENNReal.ofReal ratio ^ block) ^ (targetExponent : ℝ) =
        ENNReal.ofReal ((ratio ^ (targetExponent : ℝ)) ^ block) := by
      calc
        _ = ENNReal.ofReal (ratio ^ block) ^ (targetExponent : ℝ) :=
          congrArg (fun value : ℝ≥0∞ => value ^ (targetExponent : ℝ))
            (ENNReal.ofReal_pow hratio.le block).symm
        _ = ENNReal.ofReal ((ratio ^ block) ^ (targetExponent : ℝ)) :=
          ENNReal.ofReal_rpow_of_pos (pow_pos hratio block)
        _ = ENNReal.ofReal ((ratio ^ (targetExponent : ℝ)) ^ block) :=
          congrArg ENNReal.ofReal (Real.rpow_pow_comm hratio.le (targetExponent : ℝ) block).symm
    calc
      _ = ENNReal.ofReal ((Nat.ceil (constant * (|slope| + 3) ^ projectionExponent *
          (4 * ratio ^ projectionExponent) ^ block) : ℝ) *
            (ratio ^ (targetExponent : ℝ)) ^ block) := by
        rw [hpower, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ < 1 := ENNReal.ofReal_lt_one.2 hcost
  exact dimH_le_of_active_tree
    (active := fun level => activeWords ratio target (blockDepth block level))
    (parent := fun _ word => wordParent word)
    (branching := Nat.ceil (constant * (|slope| + 3) ^ projectionExponent *
      (4 * ratio ^ projectionExponent) ^ block))
    (ratio := ENNReal.ofReal ratio ^ block) (constant := 1)
    (exponent := targetExponent) (cover := fun _ word => dustCylinder ratio word)
    (hroot := by exact le_trans (Finset.card_le_univ _) (by simp [blockDepth]))
    (hparent := by
      intro level word hword
      exact activeWords_parent ratio target hword)
    (hchildren := by
      intro level parent hparent
      exact active_child_card_le_ceiling hratio hcontract hconstant hball hflat parent hparent)
    (hsmall := hsmall) (hconstant := ENNReal.one_ne_top) (hcost := hcostENN)
    (hdiam := by
      intro level word _
      simpa only [one_mul, blockDepth_eq_mul, pow_mul] using
        dustCylinder_ediam hratio.le hcontract word)
    (hcover := by
      intro level
      exact activeWords_cover ratio target hsubset (blockDepth block level))

/-- At every nonexceptional slope, and above the printed dimension bound,
one fixed derivative tolerance suffices for all graph pieces with that
secant tolerance. The block and constant may depend on the slope. -/
theorem exists_block_for_flat_target {ratio slope : ℝ}
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hgood : slope ∉ ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio))
    (targetExponent : ℝ≥0)
    (htarget : dimensionUpperBound ratio < (targetExponent : ℝ)) :
    ∃ block : ℕ, 0 < block ∧ ∀ target : Set (ℝ × ℝ),
      target ⊆ (cantorSet ratio).prod (cantorSet ratio) →
      (∀ left ∈ target, ∀ right ∈ target,
        |(left.2 - right.2) - slope * (left.1 - right.1)| ≤
          ratio ^ block * |left.1 - right.1|) → dimH target ≤ targetExponent := by
  have hcontract : ratio < 1 := by linarith
  obtain ⟨projectionExponent, hpositive, hupper, hcost⟩ :=
    exists_projection_exponent hratio hcontract htarget
  letI : IsProbabilityMeasure (projectedMeasure ratio slope) :=
    projectedMeasure_probability hratio.le hcontract
  obtain ⟨constant, hconstant, hball⟩ :=
    projected_probability_global_bound hratio hhalf hgood (projectedMeasure ratio slope)
      (projectedMeasure_invariant hratio.le hcontract) hpositive hupper
  obtain ⟨block, hblock, hblockCost⟩ := exists_projection_block
    (mul_nonneg hconstant.le (Real.rpow_nonneg
      (show 0 ≤ |slope| + 3 by positivity) projectionExponent)) hratio hcontract
    ((dimensionUpperBound_nonneg ratio).trans_lt htarget) hcost
  refine ⟨block, hblock, ?_⟩
  intro target hsubset hflat
  exact dimH_le_of_flat_target hratio hcontract hconstant.le hball block hblock
    targetExponent hblockCost target hsubset hflat

end LambdaCantor.First.PrefixSlopes
