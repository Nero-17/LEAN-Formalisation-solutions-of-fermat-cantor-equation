import LambdaCantor.Last.LinearReturns

noncomputable section
namespace LambdaCantor.Last

/-- The two open slope bands in Lemma 4.1 of the current paper.
The condition above one is retained separately, including in the second band. -/
def TwoBandSlopes (ratio slope : ℝ) : Prop :=
  1 < slope ∧
    ((1 / ratio - 1 - ratio < slope ∧ slope < 1 / (1 - ratio)) ∨
     (1 / ratio - 1 < slope ∧ slope < 1 / (1 - ratio - ratio ^ 2)))

/-- A compact interval lies strictly above one and inside a single band. -/
def TwoBandInterval (ratio lower upper : ℝ) : Prop :=
  1 < lower ∧ lower ≤ upper ∧
    ((1 / ratio - 1 - ratio < lower ∧ upper < 1 / (1 - ratio)) ∨
     (1 / ratio - 1 < lower ∧ upper < 1 / (1 - ratio - ratio ^ 2)))

theorem TwoBandInterval.slope {ratio lower upper slope : ℝ}
    (bands : TwoBandInterval ratio lower upper) (hlower : lower ≤ slope)
    (hupper : slope ≤ upper) : TwoBandSlopes ratio slope := by
  refine ⟨bands.1.trans_le hlower, ?_⟩
  rcases bands.2.2 with first | second
  · exact Or.inl ⟨first.1.trans_le hlower, hupper.trans_lt first.2⟩
  · exact Or.inr ⟨second.1.trans_le hlower, hupper.trans_lt second.2⟩

theorem TwoBandSlopes.common_inequalities {ratio slope : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope) :
    1 - ratio - ratio ^ 2 < ratio * slope ∧
      (1 - ratio - ratio ^ 2) * slope < 1 ∧
      (1 - 2 * ratio) * slope < 1 ∧
      1 - 2 * ratio < ratio * slope := by
  have hdenominator : 0 < 1 - ratio - ratio ^ 2 := by nlinarith
  have hdenominator_first : 0 < 1 - ratio := by linarith
  have hslope : 0 < slope := by linarith [bands.1]
  have hlower : 1 - ratio - ratio ^ 2 < ratio * slope := by
    rcases bands.2 with first | second
    · have hbound := (div_lt_iff₀ hpositive).mp (show 1 / ratio < slope + 1 + ratio by linarith [first.1])
      nlinarith
    · have hbound := (div_lt_iff₀ hpositive).mp (show 1 / ratio < slope + 1 by linarith [second.1])
      nlinarith
  have hupper : (1 - ratio - ratio ^ 2) * slope < 1 := by
    rcases bands.2 with first | second
    · have hbound := (lt_div_iff₀ hdenominator_first).mp first.2
      nlinarith [mul_pos (sq_pos_of_pos hpositive) hslope]
    · simpa only [mul_comm] using (lt_div_iff₀ hdenominator).mp second.2
  refine ⟨hlower, hupper, ?_, ?_⟩
  · have hcomparison : 1 - 2 * ratio < 1 - ratio - ratio ^ 2 := by nlinarith
    exact (mul_lt_mul_of_pos_right hcomparison hslope).trans hupper
  · nlinarith

theorem TwoBandSlopes.excludes_middle_fixed {ratio slope : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope) :
    ¬ (ratio * (1 + slope) ≤ 1 ∧ 1 ≤ slope * (1 - ratio)) := by
  rintro ⟨hlower, hupper⟩
  rcases bands.2 with first | second
  · have hbound := (lt_div_iff₀ (show 0 < 1 - ratio by linarith)).mp first.2
    nlinarith
  · have hbound := (div_lt_iff₀ hpositive).mp
      (show 1 / ratio < slope + 1 by linarith [second.1])
    nlinarith

end LambdaCantor.Last
