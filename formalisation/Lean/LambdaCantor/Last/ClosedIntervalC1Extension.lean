import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Ring

noncomputable section
open scoped Interval
namespace LambdaCantor.Last

/-- Every real C1 function on a nondegenerate closed interval has an ambient
C1 extension with the same one-sided derivatives at both endpoints. The
construction extends the continuous derivative constantly beyond the interval
and integrates it; it does not assume an extension theorem. -/
theorem closed_interval_c1_extension {function : ℝ → ℝ} {lower upper : ℝ}
    (hordered : lower < upper) (hfunction : ContDiffOn ℝ 1 function (Set.Icc lower upper)) :
    ∃ extension : ℝ → ℝ, ContDiff ℝ 1 extension ∧
      Set.EqOn extension function (Set.Icc lower upper) ∧
      Set.EqOn (deriv extension) (derivWithin function (Set.Icc lower upper)) (Set.Icc lower upper) := by
  let derivativeExtension : ℝ → ℝ := Set.IccExtend hordered.le
    (fun coordinate : Set.Icc lower upper => derivWithin function (Set.Icc lower upper) coordinate)
  have hderivativeContinuous : Continuous derivativeExtension := by
    exact (hfunction.continuousOn_derivWithin (uniqueDiffOn_Icc hordered) (le_refl _)).restrict.Icc_extend'
  have hderivativeEqual : ∀ coordinate ∈ Set.Icc lower upper,
      derivativeExtension coordinate = derivWithin function (Set.Icc lower upper) coordinate := by
    intro coordinate hcoordinate
    exact Set.IccExtend_of_mem hordered.le _ hcoordinate
  let extension : ℝ → ℝ := fun coordinate => function lower +
    ∫ point in lower..coordinate, derivativeExtension point
  have hderivatives : ∀ coordinate, HasDerivAt extension (derivativeExtension coordinate) coordinate := by
    intro coordinate
    exact (intervalIntegral.integral_hasDerivAt_right
      (hderivativeContinuous.intervalIntegrable lower coordinate)
      hderivativeContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hderivativeContinuous.continuousAt).const_add (function lower)
  have hderiv : deriv extension = derivativeExtension := by
    funext coordinate
    exact (hderivatives coordinate).deriv
  have hcontDiff : ContDiff ℝ 1 extension := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun coordinate => (hderivatives coordinate).differentiableAt, ?_⟩
    rw [hderiv]
    exact hderivativeContinuous
  refine ⟨extension, hcontDiff, ?_, ?_⟩
  · intro coordinate hcoordinate
    have hFTC : (∫ point in lower..coordinate, derivativeExtension point) =
        function coordinate - function lower := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcoordinate.1
      · exact hfunction.continuousOn.mono (Set.Icc_subset_Icc le_rfl hcoordinate.2)
      · intro point hpoint
        have hpointInterval : point ∈ Set.Icc lower upper :=
          ⟨hpoint.1.le, hpoint.2.le.trans hcoordinate.2⟩
        rw [hderivativeEqual point hpointInterval]
        exact (hfunction.differentiableOn_one point hpointInterval).hasDerivWithinAt.hasDerivAt
          (Icc_mem_nhds hpoint.1 (hpoint.2.trans_le hcoordinate.2))
      · exact hderivativeContinuous.intervalIntegrable lower coordinate
    dsimp only [extension]
    rw [hFTC]
    ring
  · intro coordinate hcoordinate
    rw [hderiv]
    exact hderivativeEqual coordinate hcoordinate

end LambdaCantor.Last
