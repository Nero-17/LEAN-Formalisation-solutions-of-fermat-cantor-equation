import LambdaCantor.Last.RationalLastActualIsolationNormalized
import LambdaCantor.Last.ArithmeticAlgebraicPowers
import LambdaCantor.Last.RationalLastArithmeticIsolation

noncomputable section
namespace LambdaCantor.Last

/-- Every positive relatively isolated point of the actual rational Fermat
intersection at c has both coordinates in Q(c). The anisotropic rectangle,
open/boundary phase cases, boundary algebraicity, actual C² function and
relative isolation of the normalized fibre are all derived internally. -/
theorem actual_rational_fermat_isolated_coordinates_at_critical
    {numerator denominator : ℕ} (denominator_positive : 0 < denominator)
    (exponent_gt_one : denominator < numerator) {ratio : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2)
    (point : intersection ((numerator : ℝ)/denominator) ratio)
    (isolated : IsOpen ({point} : Set (intersection ((numerator : ℝ)/denominator) ratio)))
    (first_positive : 0 < point.val.1) (second_positive : 0 < point.val.2) :
    point.val.1 ∈ parameterField ratio ∧ point.val.2 ∈ parameterField ratio := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have ratio_positive : 0 < ratio := by rw [critical]; nlinarith
  have ratio_less_one : ratio < 1 := by rw [critical]; nlinarith
  have rational_exponent_gt_one : 1 < (numerator : ℝ)/denominator :=
    (one_lt_div (show (0 : ℝ) < denominator by exact_mod_cast denominator_positive)).mpr
      (by exact_mod_cast exponent_gt_one)
  obtain ⟨firstWord, secondWord, tail, slope, height, tail_mem, representation, slope_identity,
      slope_lower, slope_upper, height_positive, zero, smooth, derivative⟩ :=
    exists_actual_fermat_prefix_normalization rational_exponent_gt_one ratio_positive ratio_less_one
      point first_positive second_positive
  let normalizedPoint : {value | value ∈ cantorDust ratio ∧
      normalizedFermatPrefix ((numerator : ℝ)/denominator) ratio firstWord secondWord height value = 0} :=
    ⟨tail, tail_mem, zero⟩
  have normalized_isolated := normalizedFermatPrefix_isolated_pullback ratio_positive ratio_less_one
    height_positive.ne' firstWord secondWord point normalizedPoint representation isolated
  have boundary_algebraic : slope = 1+ratio ∨ slope = 2 →
      IsAlgebraic ℚ tail.1 ∧ IsAlgebraic ℚ tail.2 := by
    intro boundary
    have ratio_algebraic := critical_ratio_algebraic critical
    have slope_mem : slope ∈ parameterField ratio := by
      rcases boundary with first_boundary | second_boundary
      · rw [first_boundary]
        exact (parameterField ratio).add_mem (parameterField ratio).one_mem (ratio_mem_parameterField ratio)
      · rw [second_boundary]
        simpa using (parameterField ratio).add_mem (parameterField ratio).one_mem (parameterField ratio).one_mem
    have coefficient_mem : ratio^secondWord.length/ratio^firstWord.length ∈ parameterField ratio :=
      (parameterField ratio).div_mem
        ((parameterField ratio).pow_mem (ratio_mem_parameterField ratio) secondWord.length)
        ((parameterField ratio).pow_mem (ratio_mem_parameterField ratio) firstWord.length)
    have tangent_identity : fermatTangentRatio ((numerator : ℝ)/denominator) point.val =
        slope/(ratio^secondWord.length/ratio^firstWord.length) := by
      rw [slope_identity]
      field_simp [(pow_pos ratio_positive firstWord.length).ne', (pow_pos ratio_positive secondWord.length).ne']
      <;> ring
    have tangent_mem : fermatTangentRatio ((numerator : ℝ)/denominator) point.val ∈ parameterField ratio := by
      rw [tangent_identity]
      exact (parameterField ratio).div_mem slope_mem coefficient_mem
    have tangent_algebraic := isAlgebraic_of_mem_parameterField ratio_algebraic tangent_mem
    have quotient_tangent_algebraic :
        IsAlgebraic ℚ ((point.val.2/point.val.1)^((numerator : ℝ)/denominator-1)) := by
      rw [← fermatTangentRatio_eq_quotient_rpow first_positive second_positive]
      exact tangent_algebraic
    have original_algebraic := positive_rational_fermat_algebraic_of_tangent first_positive second_positive
      denominator_positive exponent_gt_one point.property.2.2 quotient_tangent_algebraic
    have first_representation := congrArg Prod.fst representation
    have second_representation := congrArg Prod.snd representation
    constructor
    · apply scalarWordMap_tail_algebraic ratio_positive ratio_algebraic firstWord
      change IsAlgebraic ℚ (scalarWordMap ratio firstWord tail.1)
      rw [show scalarWordMap ratio firstWord tail.1 = point.val.1 from first_representation]
      exact original_algebraic.1
    · apply scalarWordMap_tail_algebraic ratio_positive ratio_algebraic secondWord
      change IsAlgebraic ℚ (scalarWordMap ratio secondWord tail.2)
      rw [show scalarWordMap ratio secondWord tail.2 = point.val.2 from second_representation]
      exact original_algebraic.2
  have tail_fields := critical_normalized_c2_isolated_coordinates_mem_parameterField critical
    ⟨slope_lower, slope_upper⟩
    (normalizedFermatPrefix ((numerator : ℝ)/denominator) ratio firstWord secondWord height)
    normalizedPoint normalized_isolated smooth derivative boundary_algebraic
  have original_fields := anisotropicPrefixMap_coordinates_mem_parameterField
    firstWord secondWord tail_fields.1 tail_fields.2
  rw [representation] at original_fields
  exact original_fields

/-- Actual isolated-point finiteness at the critical contraction. The only
external inputs in its dependency graph should be the registered general
Mordell and Pisot digit theorems; no isolated-classification premise remains. -/
theorem finite_isolated_actual_rational_intersection_at_critical
    {numerator denominator : ℕ} (numerator_large : 4 ≤ numerator)
    (denominator_positive : 0 < denominator) (coprime : numerator.Coprime denominator)
    (exponent_gt_one : denominator < numerator) {ratio : ℝ}
    (critical : ratio = (Real.sqrt 3-1)/2) :
    (isolatedPoints (intersection ((numerator : ℝ)/denominator) ratio)).Finite := by
  have sqrt_square := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have sqrt_nonnegative := Real.sqrt_nonneg (3 : ℝ)
  have ratio_positive : 0 < ratio := by rw [critical]; nlinarith
  have ratio_less_one : ratio < 1 := by rw [critical]; nlinarith
  apply finite_isolated_rational_intersection numerator_large denominator_positive coprime
    ratio_positive.le ratio_less_one
  intro point isolated first_positive second_positive
  exact actual_rational_fermat_isolated_coordinates_at_critical denominator_positive exponent_gt_one
    critical point isolated first_positive second_positive

end LambdaCantor.Last
