import LambdaCantor.First.RootsL1Densities

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

theorem measureDensityL1_zero : measureDensityL1 0 hasL2Density_zero = 0 := by
  apply norm_eq_zero.mp
  rw [measureDensityL1_norm]
  simp

theorem measureDensityL1_add {first second : Measure ℝ}
    (first_exists : LinearRegularity.HasL2Density first)
    (second_exists : LinearRegularity.HasL2Density second) :
    measureDensityL1 (first + second) (hasL2Density_add first_exists second_exists) =
      measureDensityL1 first first_exists + measureDensityL1 second second_exists := by
  have first_properties := measureDensity_properties first first_exists
  have second_properties := measureDensity_properties second second_exists
  have law : first + second = volume.withDensity (fun point => ENNReal.ofReal
      (measureDensity first first_exists point + measureDensity second second_exists point)) := by
    refine (congrArg₂ (fun firstMeasure secondMeasure : Measure ℝ => firstMeasure + secondMeasure)
      first_properties.2.2.2.2 second_properties.2.2.2.2).trans ?_
    rw [← withDensity_add_left first_properties.2.1.ennreal_ofReal]
    congr 1
    funext point
    exact (ENNReal.ofReal_add (first_properties.1 point) (second_properties.1 point)).symm
  rw [measureDensityL1_eq_toL1 _ _ _
    (fun point => add_nonneg (first_properties.1 point) (second_properties.1 point))
    (first_properties.2.1.add second_properties.2.1)
    (first_properties.2.2.1.add second_properties.2.2.1) law]
  exact Integrable.toL1_add _ _ _ _

theorem measureDensityL1_smul {measure : Measure ℝ}
    (density_exists : LinearRegularity.HasL2Density measure)
    (weight : ℝ≥0∞) (finite_weight : weight ≠ ∞) :
    measureDensityL1 (weight • measure) (hasL2Density_smul density_exists weight finite_weight) =
      weight.toReal • measureDensityL1 measure density_exists := by
  have properties := measureDensity_properties measure density_exists
  have law : weight • measure = volume.withDensity (fun point => ENNReal.ofReal
      (weight.toReal * measureDensity measure density_exists point)) := by
    refine (congrArg (fun sourceMeasure : Measure ℝ => weight • sourceMeasure)
      properties.2.2.2.2).trans ?_
    rw [← withDensity_smul _ properties.2.1.ennreal_ofReal]
    congr 1
    funext point
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal finite_weight]
  rw [measureDensityL1_eq_toL1 _ _ _
    (fun point => mul_nonneg ENNReal.toReal_nonneg (properties.1 point))
    (measurable_const.mul properties.2.1) (properties.2.2.1.const_mul _) law]
  exact Integrable.toL1_smul _ properties.2.2.1 weight.toReal

theorem measureDensityL1_finset_sum {Index : Type*} (indices : Finset Index)
    (measures : Index → Measure ℝ)
    (density_exists : ∀ index, LinearRegularity.HasL2Density (measures index)) :
    measureDensityL1 (∑ index ∈ indices, measures index)
      (hasL2Density_finset_sum indices measures (fun index _ => density_exists index)) =
        ∑ index ∈ indices, measureDensityL1 (measures index) (density_exists index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using measureDensityL1_zero
  | @insert index indices not_member induction_hypothesis =>
    simp only [Finset.sum_insert not_member]
    rw [measureDensityL1_add (density_exists index)
      (hasL2Density_finset_sum indices measures (fun index _ => density_exists index))]
    exact congrArg (fun rest => measureDensityL1 (measures index) (density_exists index) + rest)
      induction_hypothesis

end LambdaCantor.First.Roots
