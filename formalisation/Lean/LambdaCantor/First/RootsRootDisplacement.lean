import LambdaCantor.First.RootsTransversality
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.UniformSpace.DiscreteUniformity

noncomputable section
namespace LambdaCantor.First.Roots

theorem rootFibreData_uniform_prefix_continuity {exponent : ℝ} (data : RootFibreData exponent)
    (tolerance : ℝ) (tolerance_positive : 0 < tolerance) :
    ∃ depth : ℕ, ∀ left right : ℕ → Bool × Bool,
      (∀ index < depth, left index = right index) → |data.root right - data.root left| < tolerance := by
  letI : MetricSpace (ℕ → Bool × Bool) :=
    PiNat.metricSpaceOfDiscreteUniformity
      (fun _ => DiscreteUniformity.eq_principal_setRelId (Bool × Bool))
  have uniform := CompactSpace.uniformContinuous_of_continuous (rootFibreData_continuous_root data)
  obtain ⟨radius, radius_positive, close_roots⟩ := Metric.uniformContinuous_iff.mp uniform tolerance tolerance_positive
  obtain ⟨depth, depth_small⟩ : ∃ depth : ℕ, (1 / 2 : ℝ) ^ depth < radius :=
    exists_pow_lt_of_lt_one radius_positive (by norm_num)
  refine ⟨depth, ?_⟩
  intro left right agreement
  have close_addresses : dist right left ≤ (1 / 2 : ℝ) ^ depth :=
    PiNat.mem_cylinder_iff_dist_le.mp (fun index index_lt => (agreement index index_lt).symm)
  simpa only [Real.dist_eq] using close_roots (close_addresses.trans_lt depth_small)

private theorem transverse_inverse_bound_ordered {function : ℝ → ℝ} {left right slope : ℝ}
    (ordered : left ≤ right) (continuous : ContinuousOn function (Set.Icc left right))
    (differentiable : DifferentiableOn ℝ function (Set.Ioo left right))
    (derivative_bound : ∀ point ∈ Set.Ioo left right, slope ≤ |deriv function point|) :
    slope * |right - left| ≤ |function right - function left| := by
  rcases ordered.eq_or_lt with equal | less
  · simp [equal]
  obtain ⟨point, point_mem, derivative_identity⟩ := exists_deriv_eq_slope function less continuous differentiable
  have bound := derivative_bound point point_mem
  rw [derivative_identity, abs_div, abs_of_pos (sub_pos.mpr less)] at bound
  have result := (le_div_iff₀ (sub_pos.mpr less)).mp bound
  simpa only [abs_of_nonneg (sub_nonneg.mpr ordered)] using result

theorem transverse_inverse_bound {function : ℝ → ℝ} {left right slope : ℝ}
    (continuous : ContinuousOn function (Set.uIcc left right))
    (differentiable : ∀ point ∈ Set.uIcc left right, DifferentiableAt ℝ function point)
    (derivative_bound : ∀ point ∈ Set.uIcc left right, slope ≤ |deriv function point|) :
    slope * |right - left| ≤ |function right - function left| := by
  rcases le_total left right with ordered | ordered
  · rw [Set.uIcc_of_le ordered] at continuous differentiable derivative_bound
    exact transverse_inverse_bound_ordered ordered continuous
      (fun point point_mem => (differentiable point ⟨point_mem.1.le, point_mem.2.le⟩).differentiableWithinAt)
      (fun point point_mem => derivative_bound point ⟨point_mem.1.le, point_mem.2.le⟩)
  · rw [Set.uIcc_of_ge ordered] at continuous differentiable derivative_bound
    simpa only [abs_sub_comm] using
      transverse_inverse_bound_ordered ordered continuous
        (fun point point_mem => (differentiable point ⟨point_mem.1.le, point_mem.2.le⟩).differentiableWithinAt)
        (fun point point_mem => derivative_bound point ⟨point_mem.1.le, point_mem.2.le⟩)

/-- Actual root displacement from shared digits, once the two roots lie in
the uniform transverse neighborhood. The neighborhood size is itself derived
from RootFibreData; no residual or displacement estimate is assumed. -/
theorem rootFibreData_local_root_displacement {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ (left right : ℕ → Bool × Bool) (depth : ℕ),
      (∀ index < depth, left index = right index) → |data.root right - data.root left| < radius →
      |data.root right - data.root left| ≤
        (4 * exponent / data.derivative_lower_bound) * data.root right ^ depth := by
  obtain ⟨radius, radius_positive, transverse⟩ := rootFibreData_uniform_transversality data
  refine ⟨radius, radius_positive, ?_⟩
  intro left right depth agreement close
  have interval_band : Set.uIcc (data.root left) (data.root right) ⊆ Set.Icc data.lower data.upper :=
    Set.uIcc_subset_Icc (data.root_in_band left) (data.root_in_band right)
  have differentiable : ∀ point ∈ Set.uIcc (data.root left) (data.root right),
      DifferentiableAt ℝ
        (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength left) point := by
    intro point point_mem
    have in_band := interval_band point_mem
    exact (hasDerivAt_cylinderResidual (by linarith [data.lower_gt_quarter, in_band.1])
      (by linarith [data.upper_lt_half, in_band.2]) data.exponent_gt_one.le
      data.leftWord data.rightWord data.leftLength data.rightLength left).differentiableAt
  have derivative_bound : ∀ point ∈ Set.uIcc (data.root left) (data.root right),
      data.derivative_lower_bound / 2 ≤
        |deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength left) point| := by
    intro point point_mem
    apply (transverse left point (interval_band point_mem) _).le
    have distance_bound : |point - data.root left| ≤ |data.root right - data.root left| := by
      rcases le_total (data.root left) (data.root right) with ordered | ordered
      · rw [Set.uIcc_of_le ordered] at point_mem
        rw [abs_of_nonneg (sub_nonneg.mpr point_mem.1), abs_of_nonneg (sub_nonneg.mpr ordered)]
        linarith [point_mem.2]
      · rw [Set.uIcc_of_ge ordered] at point_mem
        rw [abs_of_nonpos (sub_nonpos.mpr point_mem.2), abs_of_nonpos (sub_nonpos.mpr ordered)]
        linarith [point_mem.1]
    exact distance_bound.trans_lt close
  have inverse := transverse_inverse_bound
    (fun point point_mem => (differentiable point point_mem).continuousAt.continuousWithinAt)
    differentiable derivative_bound
  have left_zero := (data.unique_root left (data.root left) (data.root_in_band left)).mpr rfl
  have right_zero := (data.unique_root right (data.root right) (data.root_in_band right)).mpr rfl
  have residual_bound := rootFibreData_residual_shared_prefix_bound data (data.root right)
    (data.root_in_band right) left right depth agreement
  rw [left_zero, sub_zero] at inverse
  rw [right_zero, sub_zero] at residual_bound
  have estimate := inverse.trans residual_bound
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ data.derivative_lower_bound_positive).mpr
  nlinarith

/-- The genuine exponential root-displacement bound, uniformly for all
sufficiently deep paired prefixes. All hypotheses come from RootFibreData. -/
theorem rootFibreData_root_displacement {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ minimumDepth : ℕ, ∀ (left right : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
      (∀ index < depth, left index = right index) →
      |data.root right - data.root left| ≤
        (4 * exponent / data.derivative_lower_bound) * data.root right ^ depth := by
  obtain ⟨radius, radius_positive, local_bound⟩ := rootFibreData_local_root_displacement data
  obtain ⟨minimumDepth, prefix_close⟩ := rootFibreData_uniform_prefix_continuity data radius radius_positive
  refine ⟨minimumDepth, ?_⟩
  intro left right depth depth_ge agreement
  exact local_bound left right depth agreement
    (prefix_close left right (fun index index_lt => agreement index (index_lt.trans_le depth_ge)))

end LambdaCantor.First.Roots
