import LambdaCantor.AE.DimensionMeasurabilityExtraction
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace LambdaCantor.AE

/-- A single covering set can be enlarged to an open set with any strictly
larger diameter and power-cost budgets. Zero-diameter sets are included. -/
theorem exists_open_enlargement {fibre : Set (ℝ × ℝ)} {dimension : ℝ}
    (dimension_nonnegative : 0 ≤ dimension) {scale budget : ℝ≥0∞}
    (diameter_lt : Metric.ediam fibre < scale)
    (cost_lt : Metric.ediam fibre ^ dimension < budget) :
    ∃ spatialOpen : Set (ℝ × ℝ), IsOpen spatialOpen ∧ fibre ⊆ spatialOpen ∧
      Metric.ediam spatialOpen < scale ∧ Metric.ediam spatialOpen ^ dimension < budget := by
  have radius_zero : Tendsto (fun index : ℕ => (1 : ℝ≥0) / (index+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have continuous_bound : Continuous (fun radius : ℝ≥0 =>
      Metric.ediam fibre + 2 * (radius : ℝ≥0∞)) :=
    continuous_const.add ((ENNReal.continuous_const_mul (by simp : (2 : ℝ≥0∞) ≠ ∞)).comp
      ENNReal.continuous_coe)
  have diameter_limit : Tendsto (fun index : ℕ =>
      Metric.ediam fibre + 2 * ((1 : ℝ≥0) / (index+1) : ℝ≥0)) atTop (𝓝 (Metric.ediam fibre)) := by
    simpa only [Function.comp_def, ENNReal.coe_zero, mul_zero, add_zero] using
      continuous_bound.continuousAt.tendsto.comp radius_zero
  have power_limit : Tendsto (fun index : ℕ =>
      (Metric.ediam fibre + 2 * ((1 : ℝ≥0) / (index+1) : ℝ≥0)) ^ dimension)
      atTop (𝓝 (Metric.ediam fibre ^ dimension)) := by
    simpa only [Function.comp_def] using
      (show Continuous (fun value : ℝ≥0∞ => value ^ dimension) from
        ENNReal.continuous_rpow_const).continuousAt.tendsto.comp diameter_limit
  obtain ⟨index, small_diameter, small_cost⟩ :=
    ((diameter_limit.eventually (gt_mem_nhds diameter_lt)).and
      (power_limit.eventually (gt_mem_nhds cost_lt))).exists
  refine ⟨Metric.thickening ((1 : ℝ≥0) / (index+1)) fibre,
    Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) _, ?_, ?_⟩
  · exact (Metric.ediam_thickening_le ((1 : ℝ≥0) / (index+1))).trans_lt small_diameter
  · exact (ENNReal.rpow_le_rpow
      (Metric.ediam_thickening_le ((1 : ℝ≥0) / (index+1))) dimension_nonnegative).trans_lt small_cost

end LambdaCantor.AE
