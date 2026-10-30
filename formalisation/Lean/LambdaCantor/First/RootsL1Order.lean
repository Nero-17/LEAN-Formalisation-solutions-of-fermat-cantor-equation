import LambdaCantor.First.RootsL1Densities

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

/-- Domination of finite measures gives domination of their actual density
representatives outside one Lebesgue null set. -/
theorem measureDensity_mono {first second : Measure ℝ}
    (first_exists : LinearRegularity.HasL2Density first)
    (second_exists : LinearRegularity.HasL2Density second) (dominated : first ≤ second) :
    measureDensity first first_exists ≤ᵐ[volume] measureDensity second second_exists := by
  have first_properties := measureDensity_properties first first_exists
  have second_properties := measureDensity_properties second second_exists
  have comparison : (fun point => ENNReal.ofReal (measureDensity first first_exists point)) ≤ᵐ[volume]
      (fun point => ENNReal.ofReal (measureDensity second second_exists point)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite first_properties.2.1.ennreal_ofReal
    intro subset measurable _
    rw [← withDensity_apply _ measurable, ← withDensity_apply _ measurable,
      ← first_properties.2.2.2.2, ← second_properties.2.2.2.2]
    exact dominated subset
  filter_upwards [comparison] with point comparison
  exact (ENNReal.ofReal_le_ofReal_iff (second_properties.1 point)).mp comparison

/-- The L1 cost of deleting a positive part of a kernel law is exactly its
lost mass, independently of any choices of density versions. -/
theorem measureDensityL1_distance_of_le {first second : Measure ℝ}
    (first_exists : LinearRegularity.HasL2Density first)
    (second_exists : LinearRegularity.HasL2Density second) (dominated : first ≤ second) :
    ‖measureDensityL1 second second_exists - measureDensityL1 first first_exists‖ =
      second.real Set.univ - first.real Set.univ := by
  have first_properties := measureDensity_properties first first_exists
  have second_properties := measureDensity_properties second second_exists
  have norm_integral (measure : Measure ℝ) (density_exists : LinearRegularity.HasL2Density measure) :
      ∫ point, measureDensity measure density_exists point = measure.real Set.univ := by
    rw [← measureDensityL1_norm measure density_exists]
    unfold measureDensityL1
    rw [L1.norm_of_fun_eq_integral_norm]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun point =>
      (Real.norm_of_nonneg ((measureDensity_properties measure density_exists).1 point)).symm)
  rw [measureDensityL1_distance second_exists first_exists _ _ second_properties.1 first_properties.1
    second_properties.2.1 first_properties.2.1 second_properties.2.2.1 first_properties.2.2.1
    second_properties.2.2.2.2 first_properties.2.2.2.2]
  calc
    _ = ∫ point, measureDensity second second_exists point - measureDensity first first_exists point := by
      apply integral_congr_ae
      filter_upwards [measureDensity_mono first_exists second_exists dominated] with point comparison
      exact abs_of_nonneg (sub_nonneg.mpr comparison)
    _ = _ := by
      rw [integral_sub second_properties.2.2.1 first_properties.2.2.1,
        norm_integral second second_exists, norm_integral first first_exists]

end LambdaCantor.First.Roots
