import LambdaCantor.Last.ArithmeticRationalRootCore
import LambdaCantor.Last.ArithmeticMordell

noncomputable section
namespace LambdaCantor.Last
/-- Arithmetic finiteness after radical descent. The membership hypotheses
for the rational powers are explicit: no Galois descent is silently assumed. -/
theorem finite_positive_rational_fermat_field_points
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (ratio : ℝ) :
    {point : ℝ × ℝ |
      0 < point.1 ∧ 0 < point.2 ∧
      point.1 ∈ parameterField ratio ∧ point.2 ∈ parameterField ratio ∧
      point.1 ^ ((numerator : ℝ)/denominator) ∈ parameterField ratio ∧
      point.2 ^ ((numerator : ℝ)/denominator) ∈ parameterField ratio ∧
      point.1 ^ ((numerator : ℝ)/denominator) +
        point.2 ^ ((numerator : ℝ)/denominator) = 1}.Finite := by
  let roots : (ℝ × ℝ) → (ℝ × ℝ) := fun point =>
    (point.1 ^ (1/(denominator : ℝ)), point.2 ^ (1/(denominator : ℝ)))
  have denominator_nonzero : (1 : ℝ)/(denominator : ℝ) ≠ 0 := by positivity
  refine Set.Finite.of_injOn (f := roots) ?_ ?_
    (finite_fermat_points_parameterField numerator_large ratio)
  · intro point membership
    refine ⟨denominator_root_mem_subfield (parameterField ratio) membership.1
      denominator_positive coprime membership.2.2.1 membership.2.2.2.2.1,
      denominator_root_mem_subfield (parameterField ratio) membership.2.1
        denominator_positive coprime membership.2.2.2.1 membership.2.2.2.2.2.1, ?_⟩
    dsimp [roots]
    rw [denominator_root_pow_numerator membership.1,
      denominator_root_pow_numerator membership.2.1]
    exact membership.2.2.2.2.2.2
  · intro first first_mem second second_mem equal
    apply Prod.ext
    · exact (Real.rpow_left_inj first_mem.1.le second_mem.1.le denominator_nonzero).mp
        (congrArg Prod.fst equal)
    · exact (Real.rpow_left_inj first_mem.2.1.le second_mem.2.1.le denominator_nonzero).mp
        (congrArg Prod.snd equal)

end LambdaCantor.Last

