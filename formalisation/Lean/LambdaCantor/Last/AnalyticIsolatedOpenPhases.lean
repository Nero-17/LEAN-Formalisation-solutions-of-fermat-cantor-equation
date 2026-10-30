import LambdaCantor.Last.AnalyticIsolatedAffineUncountable

noncomputable section
namespace LambdaCantor.Last

theorem periodicity_phase_weak_overlaps {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope) :
    1 ≤ slope ∧ 1-2*ratio < ratio*slope ∧ (1-2*ratio)*slope < 1 := by
  have positive : 0 < ratio := by linarith
  have complement_positive : 0 < 1-ratio := by linarith
  rcases phase with small | mixed
  · refine ⟨small.1, ?_, ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_left small.1 positive.le]
    · linarith [small.2.1]
  · have slope_positive : 0 < slope := by linarith [mixed.1]
    refine ⟨mixed.1.le, ?_, ?_⟩
    · nlinarith [mixed.2.1, mul_pos positive complement_positive]
    · nlinarith [mixed.2.2, mul_pos (mul_pos positive complement_positive) slope_positive]

theorem periodicity_phase_affine_overlap_nonempty {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope) :
    (affineOverlapCore ratio slope).Nonempty := by
  have bounds := periodicity_phase_weak_overlaps above_third less_half phase
  have positive : 0 < ratio := by linarith
  have slope_positive : 0 < slope := by linarith [bounds.1]
  refine ⟨1-ratio, mem_affineOverlapCore.mpr ⟨(false,false), (true,false), by decide, ?_, ?_⟩⟩
  all_goals
    simp only [affineChildHull, positiveLinear, LinearMap.coe_mk, AddHom.coe_mk,
      wordMap, digitPoint, Bool.false_eq_true, if_false, if_true, Prod.fst_add,
      Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero,
      smul_eq_mul, mul_zero, mul_one, add_zero, zero_add, Set.mem_Icc]
    constructor <;> nlinarith [mul_pos positive slope_positive, bounds.2.1]

/-- No affine return-existence assumption remains for an external-field slope
in either open periodicity phase. Closed overlaps, triple overlaps and child
endpoint contacts are all retained in this actual return construction. -/
theorem periodicity_phase_affine_strict_returns {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope)
    (outside : slope ∉ parameterField ratio) :
    ∀ level ∈ affineOverlapCore ratio slope, ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) level ∈ interior (affineOverlapCore ratio slope) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) level ∈ interior (affineOverlapCore ratio slope) := by
  have bounds := periodicity_phase_weak_overlaps above_third less_half phase
  exact open_phase_affine_overlap_strict_returns (by linarith) less_half bounds.1 bounds.2.1 bounds.2.2 phase outside

end LambdaCantor.Last
