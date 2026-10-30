import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter MeasureTheory Metric Set
open scoped Topology ENNReal

namespace LambdaCantor.AE

/-- The final density-point step of Theorem 4.2. The small root families need
only provide a positive proportion along one shrinking sequence at almost
every point of the parameter domain. No uniform proportion or sequence is
required across different centres. -/
theorem ae_mem_of_local_positive_proportion
    (good domain : Set ℝ) (hmeasurable : MeasurableSet good)
    (hlower : ∀ᵐ centre ∂volume, centre ∈ domain →
      ∃ (radii : ℕ → ℝ) (proportion : ℝ≥0∞),
        0 < proportion ∧ Tendsto radii atTop (𝓝[>] 0) ∧
        ∀ᶠ depth in atTop,
          proportion ≤ volume (good ∩ closedBall centre (radii depth)) /
            volume (closedBall centre (radii depth))) :
    ∀ᵐ centre ∂volume, centre ∈ domain → centre ∈ good := by
  filter_upwards [hlower,
    Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hmeasurable]
    with centre hlocal hdensity
  intro hdomain
  by_contra hnotgood
  obtain ⟨radii, proportion, hpositive, hradii, hbound⟩ := hlocal hdomain
  have hzero : Tendsto
      (fun depth => volume (good ∩ closedBall centre (radii depth)) /
        volume (closedBall centre (radii depth))) atTop (𝓝 0) := by
    simpa only [Set.indicator_of_notMem hnotgood, Function.comp_def] using hdensity.comp hradii
  exact (not_le_of_gt hpositive) (ge_of_tendsto hzero hbound)

/-- A geometric sequence of radii, as used in the manuscript, approaches zero
through strictly positive radii. -/
theorem geometric_radii_tendsto (scale : ℝ) (hscale : 0 < scale)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    Tendsto (fun depth : ℕ => scale * ratio ^ depth) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt))
  · exact Filter.Eventually.of_forall (fun depth => mul_pos hscale (pow_pos hpos depth))

end LambdaCantor.AE

