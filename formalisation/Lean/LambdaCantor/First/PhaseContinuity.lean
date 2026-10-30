import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.UniformSpace.HeineCantor

namespace LambdaCantor

/-- Convergent exponents give uniform convergence of powers on every compact
positive parameter interval. -/
theorem tendstoUniformly_phase_power {lower upper phase : ℝ}
    (hlower : 0 < lower) {phases : ℕ → ℝ}
    (hphases : Filter.Tendsto phases Filter.atTop (nhds phase)) :
    TendstoUniformly
      (fun index (ratio : Set.Icc lower upper) => (ratio : ℝ) ^ phases index)
      (fun ratio : Set.Icc lower upper => (ratio : ℝ) ^ phase) Filter.atTop := by
  have hcontinuous : Continuous (fun point : ℝ × Set.Icc lower upper =>
      (point.2 : ℝ) ^ point.1) :=
    (continuous_subtype_val.comp continuous_snd).rpow continuous_fst
      (fun point => Or.inl (ne_of_gt (lt_of_lt_of_le hlower point.2.property.1)))
  have huniform := Continuous.tendstoUniformly
    (fun (exponent : ℝ) (ratio : Set.Icc lower upper) => (ratio : ℝ) ^ exponent) hcontinuous phase
  intro entourage h_entourage
  exact hphases.eventually (huniform entourage h_entourage)

/-- The parameter derivatives converge uniformly as well. This supplies the
phase-dependent part of the normalized residual's C1 limit. -/
theorem tendstoUniformly_phase_power_derivative {lower upper phase : ℝ}
    (hlower : 0 < lower) {phases : ℕ → ℝ}
    (hphases : Filter.Tendsto phases Filter.atTop (nhds phase)) :
    TendstoUniformly
      (fun index (ratio : Set.Icc lower upper) =>
        phases index * (ratio : ℝ) ^ (phases index - 1))
      (fun ratio : Set.Icc lower upper => phase * (ratio : ℝ) ^ (phase - 1))
      Filter.atTop := by
  have hcontinuous : Continuous (fun point : ℝ × Set.Icc lower upper =>
      point.1 * (point.2 : ℝ) ^ (point.1 - 1)) :=
    continuous_fst.mul ((continuous_subtype_val.comp continuous_snd).rpow
      (continuous_fst.sub continuous_const)
      (fun point => Or.inl (ne_of_gt (lt_of_lt_of_le hlower point.2.property.1))))
  have huniform := Continuous.tendstoUniformly
    (fun (exponent : ℝ) (ratio : Set.Icc lower upper) =>
      exponent * (ratio : ℝ) ^ (exponent - 1)) hcontinuous phase
  intro entourage h_entourage
  exact hphases.eventually (huniform entourage h_entourage)

end LambdaCantor

