import LambdaCantor.AE.FreezingAverageDifferentiation

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace LambdaCantor.AE

/-- Actual Fourier-energy Lebesgue-point estimate on the manuscript parameter
range. The constant is finite, depends on the centre, and works at every fixed
positive window multiplier for all sufficiently small scales. -/
theorem ae_fullFourierEnergy_window_integral_bound
    {lower upper regularity : ℝ} (lower_positive : 0 < lower) (ordered : lower ≤ upper)
    (upper_half : upper < 1/2) (regularity_nonnegative : 0 ≤ regularity)
    (range_bound : 2*regularity <
      2*Real.log (8/3 : ℝ)/Real.log (upper/lower^3)-1) :
    ∀ᵐ centre : ℝ, centre ∈ Ioo lower upper → ∃ constant : ℝ,
      ∀ windowConstant : ℝ, 0 < windowConstant →
        ∀ᶠ scale : ℝ in 𝓝[>] (0 : ℝ),
          (∫ point in closedBall centre (windowConstant*scale),
            (fullFourierEnergy point regularity).toReal) ≤ (constant*windowConstant)*scale := by
  have local_integrable := locallyIntegrableOn_fullFourierEnergy lower_positive ordered upper_half
    regularity_nonnegative range_bound
  filter_upwards [ae_eventually_closedBall_integral_bound_of_locallyIntegrableOn
    (fun point => (fullFourierEnergy point regularity).toReal) isOpen_Ioo local_integrable]
    with centre local_bound
  intro centre_inside
  obtain ⟨constant, bound⟩ := local_bound centre_inside
  refine ⟨constant, ?_⟩
  intro windowConstant window_positive
  have radius_limit : Tendsto (fun scale : ℝ => windowConstant*scale)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using tendsto_const_nhds.mul
        (tendsto_id.mono_right nhdsWithin_le_nhds :
          Tendsto (fun scale : ℝ => scale) (𝓝[>] (0 : ℝ)) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with scale positive
      exact mul_pos window_positive positive
  filter_upwards [radius_limit.eventually bound] with scale estimate
  simpa only [mul_assoc] using estimate

end LambdaCantor.AE
