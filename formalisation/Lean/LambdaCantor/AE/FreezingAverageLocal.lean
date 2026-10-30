import LambdaCantor.AE.FreezingAverageIntegral
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set MeasureTheory
namespace LambdaCantor.AE

/-- The local version applies to an energy integrable only on the common
parameter window, rather than on the whole real line. -/
theorem weighted_freezing_energy_bound_local {ι : Type*} [Fintype ι]
    (ambient : Set ℝ) (ambient_measurable : MeasurableSet ambient)
    (intervals : ι → Set ℝ) (measurable_intervals : ∀ index, MeasurableSet (intervals index))
    (contained : ∀ index, intervals index ⊆ ambient)
    (weights : ι → ℝ) (weights_nonnegative : ∀ index, 0 ≤ weights index)
    (energy : ℝ → ℝ) (integrable : IntegrableOn energy ambient)
    (nonnegative : ∀ point ∈ ambient, 0 ≤ energy point)
    (freezing : ι → ℝ) (freezing_mem : ∀ index, freezing index ∈ intervals index)
    {length overlap : ℝ} (length_positive : 0 < length)
    (freezing_bound : ∀ index, energy (freezing index) ≤
      2/length * ∫ point in intervals index, energy point)
    (overlap_bound : ∀ point, (∑ index, (intervals index).indicator (fun _ => weights index) point) ≤ overlap) :
    (∑ index, weights index * energy (freezing index)) ≤
      (2/length) * overlap * ∫ point in ambient, energy point := by
  have integral_restriction : ∀ index,
      (∫ point in intervals index, ambient.indicator energy point) =
        ∫ point in intervals index, energy point := by
    intro index
    apply setIntegral_congr_fun (measurable_intervals index)
    intro point point_mem
    exact indicator_of_mem (contained index point_mem) energy
  have bound := weighted_freezing_energy_bound intervals measurable_intervals weights weights_nonnegative
    (ambient.indicator energy) (integrable.integrable_indicator ambient_measurable)
    (by
      intro point
      by_cases inside : point ∈ ambient
      · simpa [inside] using nonnegative point inside
      · simp [inside])
    freezing length_positive
    (by
      intro index
      rw [indicator_of_mem (contained index (freezing_mem index)) energy, integral_restriction]
      exact freezing_bound index)
    overlap_bound
  have freezing_equal : ∀ index, ambient.indicator energy (freezing index) = energy (freezing index) :=
    fun index => indicator_of_mem (contained index (freezing_mem index)) energy
  simpa only [freezing_equal, integral_indicator ambient_measurable] using bound

/-- Algebraic cancellation of the shrinking window scale gives precisely the
manuscript's depth loss. The local integral bound is supplied by a finite
Lebesgue-point estimate; it is not silently assumed uniformly in the centre. -/
theorem freezing_depth_bound {total lengthConstant overlapConstant averageConstant scale ratio dimension : ℝ}
    (depth : ℕ) (length_positive : 0 < lengthConstant) (scale_positive : 0 < scale)
    (ratio_positive : 0 < ratio) (overlap_nonnegative : 0 ≤ overlapConstant)
    {localIntegral : ℝ}
    (local_average : localIntegral ≤ averageConstant*scale)
    (weighted_bound : total ≤
      (2/(lengthConstant*scale*ratio^depth)) *
        (overlapConstant*ratio^((depth:ℝ)*dimension)) * localIntegral) :
    total ≤ (2*overlapConstant*averageConstant/lengthConstant) *
      ratio^(-(depth:ℝ)*(1-dimension)) := by
  have power_positive := pow_pos ratio_positive depth
  have factor_nonnegative : 0 ≤ (2/(lengthConstant*scale*ratio^depth)) *
      (overlapConstant*ratio^((depth:ℝ)*dimension)) := by positivity
  apply weighted_bound.trans
  calc
    _ ≤ (2/(lengthConstant*scale*ratio^depth)) *
        (overlapConstant*ratio^((depth:ℝ)*dimension)) * (averageConstant*scale) :=
      mul_le_mul_of_nonneg_left local_average factor_nonnegative
    _ = (2*overlapConstant*averageConstant/lengthConstant) *
        (ratio^((depth:ℝ)*dimension)/ratio^depth) := by
      field_simp [length_positive.ne', scale_positive.ne', power_positive.ne']
      <;> ring
    _ = _ := by
      rw [← Real.rpow_natCast ratio depth, ← Real.rpow_sub ratio_positive]
      congr 2
      ring

end LambdaCantor.AE

