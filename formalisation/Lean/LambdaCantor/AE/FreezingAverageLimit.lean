import LambdaCantor.AE.FreezingAverageLocal

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace LambdaCantor.AE

/-- A finite local-average limit gives the uniform window-integral bound used
in freezing. The precise differentiation input is exposed as a limit. -/
theorem eventually_local_integral_bound_of_finite_average
    (energy : ℝ → ℝ) (centre windowConstant limit : ℝ)
    (finite_average : Tendsto
      (fun scale : ℝ => (∫ point in Icc (centre-windowConstant*scale)
        (centre+windowConstant*scale), energy point) / scale)
      (𝓝[>] (0 : ℝ)) (𝓝 limit)) :
    ∀ᶠ scale : ℝ in 𝓝[>] (0 : ℝ),
      (∫ point in Icc (centre-windowConstant*scale)
        (centre+windowConstant*scale), energy point) ≤ (limit+1)*scale := by
  have bounded := finite_average.eventually (gt_mem_nhds (lt_add_one limit))
  filter_upwards [bounded, self_mem_nhdsWithin] with scale bound positive
  exact ((div_lt_iff₀ positive).mp bound).le

/-- Once the root-law overlap and the finite Lebesgue-point input are supplied,
the bound is uniform over all sufficiently small window scales. -/
theorem eventually_freezing_depth_bound
    (energy : ℝ → ℝ) (centre windowConstant limit : ℝ)
    {lengthConstant overlapConstant ratio dimension : ℝ}
    (length_positive : 0 < lengthConstant) (ratio_positive : 0 < ratio)
    (overlap_nonnegative : 0 ≤ overlapConstant)
    (finite_average : Tendsto
      (fun scale : ℝ => (∫ point in Icc (centre-windowConstant*scale)
        (centre+windowConstant*scale), energy point) / scale)
      (𝓝[>] (0 : ℝ)) (𝓝 limit))
    (total : ℝ → ℕ → ℝ)
    (weighted_bound : ∀ scale, 0 < scale → ∀ depth : ℕ,
      total scale depth ≤ (2/(lengthConstant*scale*ratio^depth)) *
        (overlapConstant*ratio^((depth:ℝ)*dimension)) *
          ∫ point in Icc (centre-windowConstant*scale)
            (centre+windowConstant*scale), energy point) :
    ∀ᶠ scale : ℝ in 𝓝[>] (0 : ℝ), ∀ depth : ℕ,
      total scale depth ≤ (2*overlapConstant*(limit+1)/lengthConstant) *
        ratio^(-(depth:ℝ)*(1-dimension)) := by
  filter_upwards [eventually_local_integral_bound_of_finite_average energy centre windowConstant limit finite_average,
    self_mem_nhdsWithin] with scale local_average positive
  intro depth
  exact freezing_depth_bound depth length_positive positive ratio_positive overlap_nonnegative
    local_average (weighted_bound scale positive depth)

end LambdaCantor.AE
