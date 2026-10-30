import LambdaCantor.First.ProjectionSeparation

noncomputable section
namespace LambdaCantor.First.ExternalProjection

open Filter

/-- Equal first-level translations would give exact overlaps at every positive
depth, contradicting exponential separation. -/
theorem injective_of_exponentialSeparation {ratio : ℝ} {translation : Fin 4 → ℝ}
    (hseparation : HasExponentialSeparation ratio translation) :
    Function.Injective translation := by
  rcases hseparation with ⟨rate, hrate, hlevels⟩
  intro left right hequal
  by_contra hdifferent
  rcases (hlevels.and_eventually (eventually_gt_atTop 0)).exists with
    ⟨depth, hdepth, hpositive⟩
  let leftWord : Fin depth → Fin 4 := fun position => if position.val = 0 then left else 0
  let rightWord : Fin depth → Fin 4 := fun position => if position.val = 0 then right else 0
  have hwords : leftWord ≠ rightWord := by
    intro h
    have hzero := congrFun h ⟨0, hpositive⟩
    exact hdifferent (by simpa [leftWord, rightWord] using hzero)
  have htranslations : wordTranslation ratio translation leftWord =
      wordTranslation ratio translation rightWord := by
    unfold wordTranslation
    apply Finset.sum_congr rfl
    intro position _
    by_cases hzero : position.val = 0
    · simp [leftWord, rightWord, hzero, hequal]
    · simp [leftWord, rightWord, hzero]
  have hbound := hdepth leftWord rightWord hwords
  rw [htranslations, sub_self, abs_zero] at hbound
  exact (not_le_of_gt (pow_pos hrate depth)) hbound

end LambdaCantor.First.ExternalProjection

namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory

/-- The concrete projection satisfies both separation hypotheses of Shmerkin's
theorem away from the same zero-dimensional exceptional set. -/
theorem projectedDigit_injective_of_not_collision (ratio slope : ℝ)
    (hgood : slope ∉ ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio)) :
    Function.Injective (projectedDigit ratio slope) :=
  ExternalProjection.injective_of_exponentialSeparation
    (exponentialSeparation_of_not_collision ratio slope hgood)

theorem projected_probability_global_bound
    {ratio slope : ℝ} (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hgood : slope ∉ ExceptionalSlopes.frequentCollisionSlopes (planarTranslation ratio))
    (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (hinvariant : ExternalProjection.IsFourMapInvariant measure ratio (projectedDigit ratio slope))
    {exponent : ℝ} (hpositive : 0 < exponent)
    (hexponent : exponent < min (Real.log 4 / Real.log (1 / ratio)) 1) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ center radius : ℝ, 0 < radius →
      measure (Metric.ball center radius) ≤ ENNReal.ofReal (constant * radius ^ exponent) := by
  exact ExternalProjection.shmerkin_four_map_global_ball_bound measure ratio
    (projectedDigit ratio slope) hratio (by linarith)
    (projectedDigit_injective_of_not_collision ratio slope hgood) hinvariant
    (exponentialSeparation_of_not_collision ratio slope hgood) exponent hpositive hexponent

end LambdaCantor.First.PrefixSlopes
