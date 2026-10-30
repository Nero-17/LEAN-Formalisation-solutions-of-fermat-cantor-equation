import LambdaCantor.First.RootsAffineL1
import LambdaCantor.First.RootsL1Densities

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

theorem measureDensityL1_affine_distance {first second : Measure ℝ}
    (first_exists : LinearRegularity.HasL2Density first)
    (second_exists : LinearRegularity.HasL2Density second)
    (center scale : ℝ) (scale_nonzero : scale ≠ 0) :
    ‖measureDensityL1 (first.map (fun point => center + scale * point))
        (hasL2Density_affine first_exists center scale scale_nonzero) -
      measureDensityL1 (second.map (fun point => center + scale * point))
        (hasL2Density_affine second_exists center scale scale_nonzero)‖ =
    ‖measureDensityL1 first first_exists - measureDensityL1 second second_exists‖ := by
  have first_properties := measureDensity_properties first first_exists
  have second_properties := measureDensity_properties second second_exists
  have first_law : first.map (fun point => center + scale * point) =
      volume.withDensity (fun point => ENNReal.ofReal
        (affineDensity center scale (measureDensity first first_exists) point)) := by
    exact (congrArg (fun law : Measure ℝ => law.map (fun point => center + scale * point))
      first_properties.2.2.2.2).trans
      (affine_map_withDensity center scale scale_nonzero _ first_properties.2.1)
  have second_law : second.map (fun point => center + scale * point) =
      volume.withDensity (fun point => ENNReal.ofReal
        (affineDensity center scale (measureDensity second second_exists) point)) := by
    exact (congrArg (fun law : Measure ℝ => law.map (fun point => center + scale * point))
      second_properties.2.2.2.2).trans
      (affine_map_withDensity center scale scale_nonzero _ second_properties.2.1)
  rw [measureDensityL1_distance
    (hasL2Density_affine first_exists center scale scale_nonzero)
    (hasL2Density_affine second_exists center scale scale_nonzero)
    (affineDensity center scale (measureDensity first first_exists))
    (affineDensity center scale (measureDensity second second_exists))
    (fun point => mul_nonneg (inv_nonneg.mpr (abs_nonneg scale)) (first_properties.1 _))
    (fun point => mul_nonneg (inv_nonneg.mpr (abs_nonneg scale)) (second_properties.1 _))
    (show Measurable (affineDensity center scale (measureDensity first first_exists)) by
      unfold affineDensity
      exact measurable_const.mul (first_properties.2.1.comp (by fun_prop)))
    (show Measurable (affineDensity center scale (measureDensity second second_exists)) by
      unfold affineDensity
      exact measurable_const.mul (second_properties.2.1.comp (by fun_prop)))
    (affineDensity_integrable center scale scale_nonzero _ first_properties.2.2.1)
    (affineDensity_integrable center scale scale_nonzero _ second_properties.2.2.1)
    first_law second_law,
    affineDensity_difference_integral center scale scale_nonzero,
    measureDensityL1_distance first_exists second_exists _ _ first_properties.1 second_properties.1
      first_properties.2.1 second_properties.2.1 first_properties.2.2.1 second_properties.2.2.1
      first_properties.2.2.2.2 second_properties.2.2.2.2]

end LambdaCantor.First.Roots

