import LambdaCantor.First.FrostmanPushforward
import LambdaCantor.First.RootsFrostman

noncomputable section
namespace LambdaCantor.First.Roots

open Set MeasureTheory
open scoped ENNReal NNReal

/-- The actual cylinder-incidence probability gives zero mass to every
state-space exceptional set of Hausdorff dimension at most one. -/
theorem cylinder_incidence_null_of_dimH_le_one {lower upper : ℝ}
    (quarter_lt : 1 / 4 < lower) (upper_lt : upper < 1 / 2)
    (root : (ℕ → Bool × Bool) → ℝ) (root_continuous : Continuous root)
    (root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper)
    (horizontalPrefix verticalPrefix : ℕ → Bool) (horizontalLength verticalLength : ℕ)
    {exceptional : Set (ℝ × ℝ × ℝ)} (hdimension : dimH exceptional ≤ 1) :
    pairedAddressMeasure ((cylinderIncidencePoint root horizontalPrefix verticalPrefix
      horizontalLength verticalLength) ⁻¹' exceptional) = 0 := by
  have lower_pos : 0 < lower := by linarith
  have ordered : lower ≤ upper :=
    (root_in_band (fun _ => (false, false))).1.trans
      (root_in_band (fun _ => (false, false))).2
  have lower_lt_one : lower < 1 := by linarith
  have exponent_gt_one := incidence_exponent_gt_one quarter_lt lower_lt_one
  have scale_pos : 0 < incidenceSeparationRadius lower upper
      (max horizontalLength verticalLength) := by
    unfold incidenceSeparationRadius
    apply div_pos
    · exact mul_pos (by linarith) (pow_pos lower_pos _)
    · linarith [abs_nonneg (addressParameterDerivativeBound upper)]
  have denominator_pos : 0 < incidenceSeparationRadius lower upper
      (max horizontalLength verticalLength) * lower := mul_pos scale_pos lower_pos
  have hmeasurable := (continuous_cylinderIncidencePoint lower_pos.le
    (by linarith : upper < 1) ordered root root_continuous root_in_band
    horizontalPrefix verticalPrefix horizontalLength verticalLength).measurable
  have hnull := map_null_of_image_ball_bound pairedAddressMeasure hmeasurable
    (exceptional := exceptional)
    (⟨Real.log 4 / Real.log (1 / lower), by linarith⟩ : ℝ≥0)
    (by exact_mod_cast exponent_gt_one)
    (constant := ((incidenceSeparationRadius lower upper
      (max horizontalLength verticalLength) * lower) ^
        (Real.log 4 / Real.log (1 / lower)))⁻¹)
    (cutoff := incidenceSeparationRadius lower upper (max horizontalLength verticalLength))
    (inv_pos.mpr (Real.rpow_pos_of_pos denominator_pos _)) scale_pos
  have hball : ∀ digits : ℕ → Bool × Bool, ∀ radius : ℝ, 0 < radius →
      radius < incidenceSeparationRadius lower upper (max horizontalLength verticalLength) →
      pairedAddressMeasure ((cylinderIncidencePoint root horizontalPrefix verticalPrefix
        horizontalLength verticalLength) ⁻¹'
        Metric.ball (cylinderIncidencePoint root horizontalPrefix verticalPrefix
          horizontalLength verticalLength digits) radius) ≤
        ENNReal.ofReal (((incidenceSeparationRadius lower upper
          (max horizontalLength verticalLength) * lower) ^
            (Real.log 4 / Real.log (1 / lower)))⁻¹ *
          radius ^ (Real.log 4 / Real.log (1 / lower))) := by
    intro digits radius hradius hsmall
    have h := ENNReal.ofReal_le_ofReal (cylinder_incidence_all_radius quarter_lt upper_lt
      root root_in_band horizontalPrefix verticalPrefix horizontalLength verticalLength
      digits hradius hsmall.le)
    have hpower : (radius / (incidenceSeparationRadius lower upper
          (max horizontalLength verticalLength) * lower)) ^ (Real.log 4 / Real.log (1 / lower)) =
        ((incidenceSeparationRadius lower upper (max horizontalLength verticalLength) * lower) ^
          (Real.log 4 / Real.log (1 / lower)))⁻¹ *
            radius ^ (Real.log 4 / Real.log (1 / lower)) := by
      rw [Real.div_rpow hradius.le denominator_pos.le]
      ring
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
      hpower] using h
  have hzero := hnull hball hdimension
  exact le_antisymm ((Measure.le_map_apply hmeasurable.aemeasurable exceptional).trans hzero.le)
    zero_le

end LambdaCantor.First.Roots
