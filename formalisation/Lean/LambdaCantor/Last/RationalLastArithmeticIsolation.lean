import LambdaCantor.Last.ArithmeticRationalFiniteness
import LambdaCantor.Last.AnalyticIsolatedPerfect
import LambdaCantor.Basic

noncomputable section
namespace LambdaCantor.Last

/-- Arithmetic finiteness of all relatively isolated points, with the
address-classification obligation exposed exactly where it is needed.
The possible two axis points are included explicitly. -/
theorem finite_isolated_rational_intersection
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (isolated_in_field : ∀ point : intersection ((numerator : ℝ)/denominator) ratio,
      IsOpen ({point} : Set (intersection ((numerator : ℝ)/denominator) ratio)) →
      0 < point.val.1 → 0 < point.val.2 →
        point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio) :
    (isolatedPoints (intersection ((numerator : ℝ)/denominator) ratio)).Finite := by
  have exponent_positive : 0 < (numerator : ℝ)/denominator := by positivity
  have finite_positive := finite_positive_rational_fermat_points_parameterField
    numerator_large denominator_positive coprime ratio
  have finite_axes : ({(0,1), (1,0)} : Set (ℝ × ℝ)).Finite := by simp
  refine Set.Finite.of_injOn (f := fun point : intersection ((numerator : ℝ)/denominator) ratio =>
    (point : ℝ × ℝ)) ?_ Subtype.val_injective.injOn (finite_positive.union finite_axes)
  intro point isolated
  have first_nonnegative := (cantorSet_subset_unitInterval nonnegative less_one point.property.1).1
  have second_nonnegative := (cantorSet_subset_unitInterval nonnegative less_one point.property.2.1).1
  have equation := point.property.2.2
  by_cases first_zero : point.val.1 = 0
  · apply Or.inr
    have second_one : point.val.2 = 1 := by
      apply (Real.rpow_left_inj second_nonnegative zero_le_one exponent_positive.ne').mp
      simpa [first_zero, Real.zero_rpow exponent_positive.ne'] using equation
    have point_eq : point.val = (0,1) := Prod.ext first_zero second_one
    simp [point_eq]
  · by_cases second_zero : point.val.2 = 0
    · apply Or.inr
      have first_one : point.val.1 = 1 := by
        apply (Real.rpow_left_inj first_nonnegative zero_le_one exponent_positive.ne').mp
        simpa [second_zero, Real.zero_rpow exponent_positive.ne'] using equation
      have point_eq : point.val = (1,0) := Prod.ext first_one second_zero
      simp [point_eq]
    · apply Or.inl
      have first_positive : 0 < point.val.1 := lt_of_le_of_ne first_nonnegative (Ne.symm first_zero)
      have second_positive : 0 < point.val.2 := lt_of_le_of_ne second_nonnegative (Ne.symm second_zero)
      have in_field := isolated_in_field point isolated first_positive second_positive
      exact ⟨first_positive, second_positive, in_field.1, in_field.2, equation⟩

end LambdaCantor.Last
