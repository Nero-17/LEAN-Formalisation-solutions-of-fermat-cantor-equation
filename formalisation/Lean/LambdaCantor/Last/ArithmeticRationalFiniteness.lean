import LambdaCantor.Last.ArithmeticRationalRoots
import LambdaCantor.Last.ArithmeticRationalDescent

noncomputable section
namespace LambdaCantor.Last
/-- The arithmetic conclusion required by the isolated-point argument:
the positive p/q Fermat points with coordinates in ℚ(λ) are finite when
p≥4 and p,q are coprime. Radical descent is proved in the imported module,
and the only external theorem is the general smooth plane-curve Mordell theorem. -/
theorem finite_positive_rational_fermat_points_parameterField
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (ratio : ℝ) :
    {point : ℝ × ℝ | 0 < point.1 ∧ 0 < point.2 ∧
      point.1 ∈ parameterField ratio ∧ point.2 ∈ parameterField ratio ∧
      point.1 ^ ((numerator : ℝ)/denominator) +
        point.2 ^ ((numerator : ℝ)/denominator) = 1}.Finite := by
  apply (finite_positive_rational_fermat_field_points numerator_large
    denominator_positive coprime ratio).subset
  intro point membership
  have first_power_mem : (point.1 ^ ((numerator : ℝ)/denominator)) ^ denominator ∈
      parameterField ratio := by
    rw [rational_power_pow_denominator membership.1 numerator denominator_positive]
    exact (parameterField ratio).pow_mem membership.2.2.1 numerator
  have second_power_mem : (point.2 ^ ((numerator : ℝ)/denominator)) ^ denominator ∈
      parameterField ratio := by
    rw [rational_power_pow_denominator membership.2.1 numerator denominator_positive]
    exact (parameterField ratio).pow_mem membership.2.2.2.1 numerator
  have powers_mem := positive_radicals_mem_subfield (parameterField ratio)
    (Real.rpow_pos_of_pos membership.1 _) (Real.rpow_pos_of_pos membership.2.1 _)
    membership.2.2.2.2 denominator_positive first_power_mem second_power_mem
  exact ⟨membership.1, membership.2.1, membership.2.2.1, membership.2.2.2.1,
    powers_mem.1, powers_mem.2, membership.2.2.2.2⟩

end LambdaCantor.Last

