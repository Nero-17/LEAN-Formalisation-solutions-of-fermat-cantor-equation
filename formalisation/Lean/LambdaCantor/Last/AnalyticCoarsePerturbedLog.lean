import LambdaCantor.Last.AnalyticCoarsePowerLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

theorem coarseNormalizedPowerDrop_value_error {exponent scale coordinate tolerance : ℝ}
    (hexponent : 1 < exponent) (hscale : 0 < scale) (htolerance : 0 < tolerance)
    (herror : |(1 - (1 - scale * coordinate) ^ exponent) / scale - exponent * coordinate| < tolerance) :
    |coarseNormalizedPowerDrop exponent scale coordinate - coordinate| < tolerance := by
  have hexponent_positive : 0 < exponent := by linarith
  have hidentity : coarseNormalizedPowerDrop exponent scale coordinate - coordinate =
      (((1 - (1 - scale * coordinate) ^ exponent) / scale) - exponent * coordinate) / exponent := by
    unfold coarseNormalizedPowerDrop
    field_simp [hexponent_positive.ne', hscale.ne']
    <;> ring
  rw [hidentity, abs_div, abs_of_pos hexponent_positive, div_lt_iff₀ hexponent_positive]
  exact herror.trans_le (by nlinarith [mul_pos htolerance (sub_pos.mpr hexponent)])

/-- Explicit denominator/numerator estimate for the actual logarithm.
The tolerance choices are precisely the concrete C1 margins used below. -/
theorem coarsePowerLog_relative_error {exponent scale lower coordinate tolerance eta : ℝ}
    (hlower : 0 < lower) (hcoordinate : coordinate ∈ Set.Icc lower 1)
    (htolerance : 0 < tolerance) (heta : 0 < eta)
    (htolerance_lower : tolerance ≤ lower / 4) (htolerance_eta : tolerance ≤ eta * lower / 8)
    (hvalue : |coarseNormalizedPowerDrop exponent scale coordinate - coordinate| < tolerance)
    (hfactor : |coarsePowerFactor exponent scale coordinate - 1| < tolerance) :
    lower / 2 < coarseNormalizedPowerDrop exponent scale coordinate ∧
      |coordinate * coarsePowerFactor exponent scale coordinate /
        coarseNormalizedPowerDrop exponent scale coordinate - 1| < eta := by
  have hcoordinate_positive : 0 < coordinate := hlower.trans_le hcoordinate.1
  have hdenominator : lower / 2 < coarseNormalizedPowerDrop exponent scale coordinate := by
    linarith only [hlower, hcoordinate.1, htolerance_lower, (abs_lt.mp hvalue).1]
  have hdenominator_positive : 0 < coarseNormalizedPowerDrop exponent scale coordinate := by linarith
  have hfirst_error : |coordinate * (coarsePowerFactor exponent scale coordinate - 1)| < tolerance := by
    rw [abs_mul, abs_of_pos hcoordinate_positive]
    exact (mul_le_of_le_one_left (abs_nonneg _) hcoordinate.2).trans_lt hfactor
  have hsecond_error : |coordinate - coarseNormalizedPowerDrop exponent scale coordinate| < tolerance := by
    simpa only [abs_sub_comm] using hvalue
  have hnumerator : |coordinate * (coarsePowerFactor exponent scale coordinate - 1) +
      (coordinate - coarseNormalizedPowerDrop exponent scale coordinate)| < 2 * tolerance :=
    (abs_add_le _ _).trans_lt (by linarith)
  have hidentity : coordinate * coarsePowerFactor exponent scale coordinate /
      coarseNormalizedPowerDrop exponent scale coordinate - 1 =
      (coordinate * (coarsePowerFactor exponent scale coordinate - 1) +
        (coordinate - coarseNormalizedPowerDrop exponent scale coordinate)) /
          coarseNormalizedPowerDrop exponent scale coordinate := by
    field_simp [hdenominator_positive.ne']
    <;> ring
  refine ⟨hdenominator, ?_⟩
  rw [hidentity, abs_div, abs_of_pos hdenominator_positive, div_lt_iff₀ hdenominator_positive]
  have hscaled := mul_lt_mul_of_pos_left hdenominator heta
  nlinarith

/-- Uniform value/derivative control of the actual normalized power logarithm
on any fixed positive coordinate interval. No C1 stability premise is assumed. -/
theorem coarsePowerLog_uniform_relative_derivative {exponent lower eta : ℝ}
    (hexponent : 1 < exponent) (hlower : 0 < lower) (heta : 0 < eta) :
    ∃ cutoff > 0, ∀ scale : ℝ, 0 < scale → scale < cutoff →
      ∀ coordinate ∈ Set.Icc lower 1,
        lower / 2 < coarseNormalizedPowerDrop exponent scale coordinate ∧
        HasDerivAt (coarsePowerLog exponent scale)
          (coarsePowerFactor exponent scale coordinate /
            coarseNormalizedPowerDrop exponent scale coordinate) coordinate ∧
        |coordinate * coarsePowerFactor exponent scale coordinate /
          coarseNormalizedPowerDrop exponent scale coordinate - 1| < eta := by
  let tolerance := min (lower / 4) (eta * lower / 8)
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  obtain ⟨cutoff, hcutoff, hestimates⟩ := real_power_uniform_value_and_partial exponent htolerance
  refine ⟨cutoff, hcutoff, ?_⟩
  intro scale hscale hsmall coordinate hcoordinate
  have hunit : coordinate ∈ Set.Icc (0 : ℝ) 1 := ⟨hlower.le.trans hcoordinate.1, hcoordinate.2⟩
  have hraw := hestimates scale hscale hsmall coordinate hunit
  have hvalue := coarseNormalizedPowerDrop_value_error hexponent hscale htolerance hraw.1
  have hrelative := coarsePowerLog_relative_error hlower hcoordinate htolerance heta
    (min_le_left _ _) (min_le_right _ _) hvalue hraw.2
  refine ⟨hrelative.1, coarsePowerLog_hasDerivAt hexponent hscale.ne' ?_, hrelative.2⟩
  linarith [hrelative.1]

theorem coarseLogCoordinateMap_uniform_derivative {exponent ratio eta : ℝ}
    (hexponent : 1 < exponent) (hratio : 0 ≤ ratio) (hless : ratio < 1) (heta : 0 < eta) :
    ∃ cutoff > 0, ∀ scale : ℝ, 0 < scale → scale < cutoff →
      ∀ coordinate ∈ Set.Icc (Real.log (1 - ratio)) 0,
        HasDerivAt (coarseLogCoordinateMap exponent scale)
          (Real.exp coordinate * coarsePowerFactor exponent scale (Real.exp coordinate) /
            coarseNormalizedPowerDrop exponent scale (Real.exp coordinate)) coordinate ∧
        |Real.exp coordinate * coarsePowerFactor exponent scale (Real.exp coordinate) /
          coarseNormalizedPowerDrop exponent scale (Real.exp coordinate) - 1| < eta := by
  have hlower : 0 < 1 - ratio := by linarith
  obtain ⟨cutoff, hcutoff, huniform⟩ := coarsePowerLog_uniform_relative_derivative hexponent hlower heta
  refine ⟨cutoff, hcutoff, ?_⟩
  intro scale hscale hsmall coordinate hcoordinate
  have hexp_bounds : Real.exp coordinate ∈ Set.Icc (1 - ratio) 1 := by
    constructor
    · rw [← Real.exp_log hlower]
      exact Real.exp_le_exp.mpr hcoordinate.1
    · simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hcoordinate.2
  have hbound := huniform scale hscale hsmall (Real.exp coordinate) hexp_bounds
  refine ⟨coarseLogCoordinateMap_hasDerivAt hexponent hscale.ne' ?_, hbound.2.2⟩
  linarith [hbound.1]

theorem coarseLogCoordinateMap_uniform_increments {exponent ratio eta : ℝ}
    (hexponent : 1 < exponent) (hratio : 0 ≤ ratio) (hless : ratio < 1) (heta : 0 < eta) :
    ∃ cutoff > 0, ∀ scale : ℝ, 0 < scale → scale < cutoff →
      ContinuousOn (coarseLogCoordinateMap exponent scale) (Set.Icc (Real.log (1 - ratio)) 0) ∧
      ∀ first ∈ Set.Icc (Real.log (1 - ratio)) 0,
      ∀ second ∈ Set.Icc (Real.log (1 - ratio)) 0, first ≤ second →
        (1 - eta) * (second - first) ≤
          coarseLogCoordinateMap exponent scale second - coarseLogCoordinateMap exponent scale first ∧
        coarseLogCoordinateMap exponent scale second - coarseLogCoordinateMap exponent scale first ≤
          (1 + eta) * (second - first) := by
  obtain ⟨cutoff, hcutoff, hderivatives⟩ := coarseLogCoordinateMap_uniform_derivative hexponent hratio hless heta
  refine ⟨cutoff, hcutoff, ?_⟩
  intro scale hscale hsmall
  have hcontinuous : ContinuousOn (coarseLogCoordinateMap exponent scale)
      (Set.Icc (Real.log (1 - ratio)) 0) :=
    fun coordinate hcoordinate => ((hderivatives scale hscale hsmall coordinate hcoordinate).1).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ (coarseLogCoordinateMap exponent scale)
      (interior (Set.Icc (Real.log (1 - ratio)) 0)) :=
    fun coordinate hcoordinate => ((hderivatives scale hscale hsmall coordinate
      (interior_subset hcoordinate)).1).differentiableAt.differentiableWithinAt
  refine ⟨hcontinuous, ?_⟩
  intro first hfirst second hsecond horder
  constructor
  · apply (convex_Icc (Real.log (1 - ratio)) 0).mul_sub_le_image_sub_of_le_deriv
      hcontinuous hdifferentiable _ first hfirst second hsecond horder
    intro coordinate hcoordinate
    rw [((hderivatives scale hscale hsmall coordinate (interior_subset hcoordinate)).1).deriv]
    have hbound := (abs_lt.mp (hderivatives scale hscale hsmall coordinate (interior_subset hcoordinate)).2).1
    linarith
  · apply (convex_Icc (Real.log (1 - ratio)) 0).image_sub_le_mul_sub_of_deriv_le
      hcontinuous hdifferentiable _ first hfirst second hsecond horder
    intro coordinate hcoordinate
    rw [((hderivatives scale hscale hsmall coordinate (interior_subset hcoordinate)).1).deriv]
    have hbound := (abs_lt.mp (hderivatives scale hscale hsmall coordinate (interior_subset hcoordinate)).2).2
    linarith

end LambdaCantor.Last
