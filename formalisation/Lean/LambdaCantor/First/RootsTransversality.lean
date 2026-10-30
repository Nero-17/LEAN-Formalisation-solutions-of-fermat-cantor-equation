import LambdaCantor.First.RootsResidualEstimates
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Filter Topology
namespace LambdaCantor.First.Roots

/-- Compactness upgrades continuity of the actual derivative to one common
parameter neighborhood of all roots. The interval projection handles roots
at either endpoint without extending the root-data assumptions. -/
theorem rootFibreData_uniform_derivative_near_root {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ (digits : ℕ → Bool × Bool) (ratio : ℝ),
      ratio ∈ Set.Icc data.lower data.upper → |ratio - data.root digits| < radius →
      |deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits) ratio -
        deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits)
          (data.root digits)| < data.derivative_lower_bound / 2 := by
  let shiftedDerivative : ℝ → (ℕ → Bool × Bool) → ℝ := fun displacement digits =>
    deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits)
      (Set.projIcc data.lower data.upper data.ordered (data.root digits + displacement))
  have shifted_continuous : Continuous (Function.uncurry shiftedDerivative) := by
    let derivativeOnBand : ((ℕ → Bool × Bool) × Set.Icc data.lower data.upper) → ℝ :=
      fun point => deriv
        (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength point.1)
        point.2
    let shiftedState : (ℝ × (ℕ → Bool × Bool)) →
        ((ℕ → Bool × Bool) × Set.Icc data.lower data.upper) := fun point =>
      (point.2, Set.projIcc data.lower data.upper data.ordered (data.root point.2 + point.1))
    have derivative_continuous : Continuous derivativeOnBand :=
      rootFibreData_continuous_residual_derivative data
    have root_continuous : Continuous (fun point : ℝ × (ℕ → Bool × Bool) => data.root point.2) :=
      (rootFibreData_continuous_root data).comp
        (continuous_snd : Continuous (fun point : ℝ × (ℕ → Bool × Bool) => point.2))
    have displaced_continuous : Continuous (fun point : ℝ × (ℕ → Bool × Bool) =>
        data.root point.2 + point.1) := root_continuous.add continuous_fst
    have projected_continuous : Continuous (fun point : ℝ × (ℕ → Bool × Bool) =>
        Set.projIcc data.lower data.upper data.ordered (data.root point.2 + point.1)) :=
      (show Continuous (Set.projIcc data.lower data.upper data.ordered) from continuous_projIcc).comp
        displaced_continuous
    have state_continuous : Continuous shiftedState :=
      (continuous_snd : Continuous (fun point : ℝ × (ℕ → Bool × Bool) => point.2)).prodMk
        projected_continuous
    have composed : Continuous (derivativeOnBand ∘ shiftedState) :=
      Continuous.comp (f := shiftedState) (g := derivativeOnBand)
        derivative_continuous state_continuous
    have identification : derivativeOnBand ∘ shiftedState = Function.uncurry shiftedDerivative := by
      funext point
      rfl
    rw [← identification]
    exact composed
  have uniform := Continuous.tendstoUniformly shiftedDerivative shifted_continuous 0
  have eventual := (Metric.tendstoUniformly_iff.mp uniform)
    (data.derivative_lower_bound / 2) (by linarith [data.derivative_lower_bound_positive])
  obtain ⟨radius, radius_positive, radius_property⟩ := Metric.mem_nhds_iff.mp eventual
  refine ⟨radius, radius_positive, ?_⟩
  intro digits ratio in_band close
  have displacement_mem : ratio - data.root digits ∈ Metric.ball (0 : ℝ) radius := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using close
  have estimate := radius_property displacement_mem digits
  have shifted_ratio : data.root digits + (ratio - data.root digits) = ratio := by ring
  simpa only [shiftedDerivative, add_zero, shifted_ratio,
    Set.projIcc_of_mem data.ordered (data.root_in_band digits), Set.projIcc_of_mem data.ordered in_band,
    Real.dist_eq, abs_sub_comm] using estimate

theorem rootFibreData_uniform_transversality {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ (digits : ℕ → Bool × Bool) (ratio : ℝ),
      ratio ∈ Set.Icc data.lower data.upper → |ratio - data.root digits| < radius →
      data.derivative_lower_bound / 2 <
        |deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits) ratio| := by
  obtain ⟨radius, radius_positive, derivative_close⟩ := rootFibreData_uniform_derivative_near_root data
  refine ⟨radius, radius_positive, ?_⟩
  intro digits ratio in_band close
  have estimate := derivative_close digits ratio in_band close
  have transverse := data.transverse digits
  have triangle := abs_sub_abs_le_abs_sub
    (deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits)
      (data.root digits))
    (deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits) ratio)
  rw [abs_sub_comm] at triangle
  linarith

end LambdaCantor.First.Roots
