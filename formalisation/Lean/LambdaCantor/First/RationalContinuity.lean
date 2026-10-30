import LambdaCantor.First.RationalMain

noncomputable section
open Set Filter Topology
namespace LambdaCantor.First

/-- A punctured limit on the exponent half-line characterizes its continuity
points, including the endpoint exponent two. -/
theorem continuousWithinAt_iff_of_punctured_limit
    (function : ℝ → ℝ) (value center : ℝ) (hcenter : 2 ≤ center)
    (hlimit : Tendsto function
      (𝓝[{x : ℝ | 2 ≤ x ∧ x ≠ center}] center) (𝓝 value)) :
    ContinuousWithinAt function (Ici 2) center ↔ function center = value := by
  constructor
  · intro hcontinuous
    have hright : Tendsto function (𝓝[>] center) (𝓝 value) :=
      hlimit.mono_left (nhdsWithin_mono _ (by
        intro x hx
        exact ⟨hcenter.trans hx.le, ne_of_gt hx⟩))
    have hcontinuousRight : Tendsto function (𝓝[>] center) (𝓝 (function center)) :=
      hcontinuous.mono (by intro x hx; exact hcenter.trans hx.le)
    exact tendsto_nhds_unique hcontinuousRight hright
  · intro hvalue
    apply continuousWithinAt_sdiff_self.mp
    change Tendsto function
      (𝓝[{x : ℝ | 2 ≤ x ∧ x ≠ center}] center) (𝓝 (function center))
    rwa [hvalue]

end LambdaCantor.First
