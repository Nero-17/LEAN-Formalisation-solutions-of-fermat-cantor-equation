import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section
namespace LambdaCantor.First

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- A finite constant in a local diameter estimate does not affect nullity
of sets below the mass exponent. This uses actual measure domination. -/
theorem measure_zero_of_local_diameter_bound {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (measure : Measure X)
    (exponent : ℝ≥0) {constant cutoff : ℝ≥0∞}
    (hconstant : constant ≠ 0) (hfinite : constant ≠ ∞) (hcutoff : 0 < cutoff)
    (hbound : ∀ target : Set X, Metric.ediam target ≤ cutoff →
      measure target ≤ constant * Metric.ediam target ^ (exponent : ℝ))
    {exceptional : Set X} (hdimension : dimH exceptional < exponent) :
    measure exceptional = 0 := by
  have hdomination : constant⁻¹ • measure ≤ μH[(exponent : ℝ)] := by
    apply Measure.le_hausdorffMeasure (exponent : ℝ) (constant⁻¹ • measure)
      cutoff hcutoff
    intro target htarget
    calc
      (constant⁻¹ • measure) target = constant⁻¹ * measure target := by simp
      _ ≤ constant⁻¹ * (constant * Metric.ediam target ^ (exponent : ℝ)) :=
        mul_le_mul_left' (hbound target htarget) _
      _ = Metric.ediam target ^ (exponent : ℝ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hconstant hfinite, one_mul]
  have hzero : (constant⁻¹ • measure) exceptional = 0 := by
    apply le_antisymm
    · exact (Measure.le_iff'.1 hdomination exceptional).trans
        (hausdorffMeasure_of_dimH_lt hdimension).le
    · exact zero_le
  have hproduct : constant⁻¹ * measure exceptional = 0 := by simpa using hzero
  exact (mul_eq_zero.mp hproduct).resolve_left (ENNReal.inv_ne_zero.mpr hfinite)

/-- Open-ball estimates pass to the exact extended diameter by taking radii
down to the diameter. This includes zero-diameter sets. -/
theorem diameter_bound_of_local_ball_bound {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] (measure : Measure X) (exponent : ℝ)
    {constant cutoff : ℝ≥0∞} (hfinite : constant ≠ ∞)
    (hball : ∀ center : X, ∀ radius : ℝ≥0∞, 0 < radius → radius < cutoff →
      measure (EMetric.ball center radius) ≤ constant * radius ^ exponent)
    {target : Set X} (htarget : Metric.ediam target < cutoff) :
    measure target ≤ constant * Metric.ediam target ^ exponent := by
  rcases target.eq_empty_or_nonempty with rfl | ⟨center, hcenter⟩
  · simp
  haveI : NeBot (𝓝[>] Metric.ediam target) :=
    nhdsWithin_Ioi_neBot' ⟨cutoff, htarget⟩ le_rfl
  have hlimit : Tendsto (fun radius : ℝ≥0∞ => constant * radius ^ exponent)
      (𝓝[>] Metric.ediam target)
      (𝓝 (constant * Metric.ediam target ^ exponent)) :=
    (ENNReal.Tendsto.const_mul
      ENNReal.continuous_rpow_const.continuousAt.tendsto (Or.inr hfinite)).mono_left
      nhdsWithin_le_nhds
  apply ge_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds htarget)] with radius hgreater hless
  apply (measure_mono (show target ⊆ EMetric.ball center radius from ?_)).trans
    (hball center radius ((zero_le : 0 ≤ Metric.ediam target).trans_lt hgreater) hless)
  intro point hpoint
  exact (Metric.edist_le_ediam_of_mem hpoint hcenter).trans_lt hgreater

/-- A local Frostman estimate of exponent strictly greater than one excludes
every set of Hausdorff dimension at most one. -/
theorem measure_zero_of_dimH_le_one_of_ball_bound {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (measure : Measure X)
    (exponent : ℝ≥0) (hexponent : 1 < exponent)
    {constant cutoff smallCutoff : ℝ≥0∞}
    (hconstant : constant ≠ 0) (hfinite : constant ≠ ∞)
    (hsmall : 0 < smallCutoff) (hcutoff : smallCutoff < cutoff)
    (hball : ∀ center : X, ∀ radius : ℝ≥0∞, 0 < radius → radius < cutoff →
      measure (EMetric.ball center radius) ≤ constant * radius ^ (exponent : ℝ))
    {exceptional : Set X} (hdimension : dimH exceptional ≤ 1) :
    measure exceptional = 0 := by
  apply measure_zero_of_local_diameter_bound measure exponent hconstant hfinite hsmall
  · intro target htarget
    exact diameter_bound_of_local_ball_bound measure (exponent : ℝ) hfinite hball
      (htarget.trans_lt hcutoff)
  · exact hdimension.trans_lt (by exact_mod_cast hexponent)

end LambdaCantor.First
