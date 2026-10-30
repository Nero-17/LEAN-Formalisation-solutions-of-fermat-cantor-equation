import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.RealPowers

/-- The coefficient forcing the half-normalized affine level theta uses
1-2*theta. The denominator is eventually positive even when that factor is
negative. The horizontal normalized derivative approaches the target slope
uniformly over the full unit interval. -/
theorem deep_source_horizontal_error (exponent firstEndpoint secondEndpoint scaleRatio level : ℝ)
    (first_positive : 0 < firstEndpoint) (second_positive : 0 < secondEndpoint)
    (epsilon : ℝ) (epsilon_positive : 0 < epsilon) :
    ∃ delta > 0, ∀ horizontalScale verticalScale : ℝ,
      0 < horizontalScale → 0 < verticalScale →
      horizontalScale < delta → verticalScale < delta →
      horizontalScale/verticalScale = scaleRatio →
      let coefficient := firstEndpoint^exponent/
        (secondEndpoint+verticalScale*(1-2*level))
      0 < coefficient ∧
      -((firstEndpoint^exponent)-coefficient*(secondEndpoint+verticalScale))/
        (2*coefficient*verticalScale) = level ∧
      ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
        |(exponent*horizontalScale*(firstEndpoint+horizontalScale*coordinate)^(exponent-1))/
          (2*coefficient*verticalScale)-
          (exponent*scaleRatio*secondEndpoint/firstEndpoint)/2| < epsilon := by
  have power_positive : 0 < firstEndpoint^exponent := Real.rpow_pos_of_pos first_positive _
  have field_continuous : ContinuousAt
      (fun point : ℝ × ℝ => (exponent*scaleRatio/(2*firstEndpoint^exponent))*
        point.2*point.1^(exponent-1)) (firstEndpoint,secondEndpoint) :=
    (continuousAt_const.mul continuous_snd.continuousAt).mul
      ((show ContinuousAt (fun point : ℝ × ℝ => point.1) (firstEndpoint,secondEndpoint) from
        continuous_fst.continuousAt).rpow_const (Or.inl first_positive.ne'))
  have center_identity :
      (exponent*scaleRatio/(2*firstEndpoint^exponent))*secondEndpoint*firstEndpoint^(exponent-1) =
        (exponent*scaleRatio*secondEndpoint/firstEndpoint)/2 := by
    rw [Real.rpow_sub_one first_positive.ne']
    field_simp [power_positive.ne', first_positive.ne']
    <;> ring
  obtain ⟨radius, radius_positive, close⟩ :=
    Metric.continuousAt_iff.mp field_continuous epsilon epsilon_positive
  let delta := min radius (min (radius/(|1-2*level|+1))
    (secondEndpoint/(2*(|1-2*level|+1))))
  have factor_positive : 0 < |1-2*level|+1 := by positivity
  have delta_positive : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta, delta_positive, ?_⟩
  intro horizontalScale verticalScale horizontal_positive vertical_positive
    horizontal_small vertical_small scale_equation
  have horizontal_radius : horizontalScale < radius :=
    horizontal_small.trans_le (min_le_left _ _)
  have vertical_radius : verticalScale < radius/(|1-2*level|+1) :=
    vertical_small.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have vertical_endpoint : verticalScale < secondEndpoint/(2*(|1-2*level|+1)) :=
    vertical_small.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have vertical_error_radius : verticalScale*|1-2*level| < radius := by
    have cleared := (lt_div_iff₀ factor_positive).mp vertical_radius
    nlinarith [vertical_positive]
  have vertical_error_endpoint : verticalScale*|1-2*level| < secondEndpoint/2 := by
    have cleared := (lt_div_iff₀ (by positivity : 0 < 2*(|1-2*level|+1))).mp vertical_endpoint
    nlinarith [vertical_positive]
  have denominator_positive : 0 < secondEndpoint+verticalScale*(1-2*level) := by
    have absolute := neg_abs_le (1-2*level)
    nlinarith [mul_le_mul_of_nonneg_left absolute vertical_positive.le]
  have coefficient_positive : 0 < firstEndpoint^exponent/
      (secondEndpoint+verticalScale*(1-2*level)) := div_pos power_positive denominator_positive
  refine ⟨coefficient_positive, ?_, ?_⟩
  · field_simp [power_positive.ne', denominator_positive.ne', vertical_positive.ne']
    <;> ring
  · intro coordinate coordinate_bounds
    have horizontal_error : |horizontalScale*coordinate| < radius := by
      rw [abs_of_nonneg (mul_nonneg horizontal_positive.le coordinate_bounds.1)]
      exact (mul_le_of_le_one_right horizontal_positive.le coordinate_bounds.2).trans_lt horizontal_radius
    have vertical_error : |verticalScale*(1-2*level)| < radius := by
      rw [abs_mul, abs_of_pos vertical_positive]
      exact vertical_error_radius
    have point_close :
        dist ((firstEndpoint+horizontalScale*coordinate,
          secondEndpoint+verticalScale*(1-2*level)) : ℝ × ℝ)
          (firstEndpoint,secondEndpoint) < radius := by
      simpa only [Prod.dist_eq, Real.dist_eq, add_sub_cancel_left, max_lt_iff] using
        And.intro horizontal_error vertical_error
    have estimate := close point_close
    rw [Real.dist_eq] at estimate
    rw [center_identity] at estimate
    have scale_cleared : horizontalScale = scaleRatio*verticalScale :=
      (div_eq_iff vertical_positive.ne').mp scale_equation
    have horizontal_identity :
        (exponent*horizontalScale*(firstEndpoint+horizontalScale*coordinate)^(exponent-1))/
          (2*(firstEndpoint^exponent/(secondEndpoint+verticalScale*(1-2*level)))*verticalScale) =
        (exponent*scaleRatio/(2*firstEndpoint^exponent))*
          (secondEndpoint+verticalScale*(1-2*level))*
          (firstEndpoint+horizontalScale*coordinate)^(exponent-1) := by
      rw [scale_cleared]
      field_simp [power_positive.ne', denominator_positive.ne', vertical_positive.ne']
      <;> ring
    rw [horizontal_identity]
    exact estimate

end LambdaCantor.RealPowers

