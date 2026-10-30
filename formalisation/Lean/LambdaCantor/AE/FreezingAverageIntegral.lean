import LambdaCantor.AE.FreezingAverage
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Set MeasureTheory
namespace LambdaCantor.AE

/-- Weighted overlap controls the sum of interval energy integrals. Energy is
used directly; no square-root variable is introduced. -/
theorem weighted_interval_integral_bound {ι : Type*} [Fintype ι]
    (intervals : ι → Set ℝ) (measurable_intervals : ∀ index, MeasurableSet (intervals index))
    (weights : ι → ℝ) (energy : ℝ → ℝ) (integrable : Integrable energy)
    (nonnegative : ∀ point, 0 ≤ energy point) {overlap : ℝ}
    (overlap_bound : ∀ point, (∑ index, (intervals index).indicator (fun _ => weights index) point) ≤ overlap) :
    (∑ index, weights index * ∫ point in intervals index, energy point) ≤ overlap * ∫ point, energy point := by
  classical
  have integrable_terms : ∀ index, Integrable (fun point =>
      weights index * (intervals index).indicator energy point) := fun index =>
    (integrable.indicator (measurable_intervals index)).const_mul (weights index)
  have integral_identity :
      (∫ point, ∑ index, weights index * (intervals index).indicator energy point) =
      ∑ index, weights index * ∫ point in intervals index, energy point := by
    rw [integral_finsetSum _ (fun index _ => integrable_terms index)]
    apply Finset.sum_congr rfl
    intro index _
    rw [integral_const_mul, integral_indicator (measurable_intervals index)]
  rw [← integral_identity, ← integral_const_mul]
  apply integral_mono (integrable_finset_sum _ (fun index _ => integrable_terms index))
    (integrable.const_mul overlap)
  intro point
  have identity :
      (∑ index, weights index * (intervals index).indicator energy point) =
      (∑ index, (intervals index).indicator (fun _ => weights index) point) * energy point := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro index _
    by_cases inside : point ∈ intervals index <;> simp [inside]
  change (∑ index, weights index * (intervals index).indicator energy point) ≤ overlap * energy point
  rw [identity]
  exact mul_le_mul_of_nonneg_right (overlap_bound point) (nonnegative point)

/-- Combining chosen freezing points with weighted overlap. The equal interval
length is explicit, as it is in the manuscript construction. -/
theorem weighted_freezing_energy_bound {ι : Type*} [Fintype ι]
    (intervals : ι → Set ℝ) (measurable_intervals : ∀ index, MeasurableSet (intervals index))
    (weights : ι → ℝ) (weights_nonnegative : ∀ index, 0 ≤ weights index)
    (energy : ℝ → ℝ) (integrable : Integrable energy) (nonnegative : ∀ point, 0 ≤ energy point)
    (freezing : ι → ℝ) {length overlap : ℝ} (length_positive : 0 < length)
    (freezing_bound : ∀ index, energy (freezing index) ≤
      2/length * ∫ point in intervals index, energy point)
    (overlap_bound : ∀ point, (∑ index, (intervals index).indicator (fun _ => weights index) point) ≤ overlap) :
    (∑ index, weights index * energy (freezing index)) ≤
      (2/length) * overlap * ∫ point, energy point := by
  calc
    _ ≤ ∑ index, weights index * (2/length * ∫ point in intervals index, energy point) :=
      Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (freezing_bound index) (weights_nonnegative index)
    _ = (2/length) * ∑ index, weights index * ∫ point in intervals index, energy point := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ ≤ (2/length) * (overlap * ∫ point, energy point) :=
      mul_le_mul_of_nonneg_left
        (weighted_interval_integral_bound intervals measurable_intervals weights energy integrable nonnegative overlap_bound)
        (by positivity)
    _ = _ := by ring

end LambdaCantor.AE
