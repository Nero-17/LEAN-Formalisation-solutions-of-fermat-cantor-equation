import LambdaCantor.First.RootsKernelLinearization
import LambdaCantor.First.RootsParameterTaylor
import LambdaCantor.First.RootsPrefixResidualDerivative

noncomputable section
namespace LambdaCantor.First.Roots

private theorem kernel_remainder_identity (derivative otherDerivative displacement linearTerm residual : ℝ) :
    derivative * displacement + linearTerm =
      -(-residual - otherDerivative * displacement) - (residual - linearTerm) +
        (derivative - otherDerivative) * displacement := by ring

/-- The complete frozen kernel approximates the true root for every fresh
tail in its cylinder, with the manuscript's unnormalized quadratic scale.
All constants and all estimates are derived from the concrete root data. -/
theorem rootFibreData_kernel_approximates_root {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∃ minimumDepth : ℕ,
      ∀ (representative digits : ℕ → Bool × Bool) (depth : ℕ), minimumDepth ≤ depth →
        (∀ index < depth, representative index = digits index) →
        |data.root digits - rootKernelValue data representative digits depth| ≤
          constant * ((depth : ℝ) + 1) * data.root representative ^ (2 * depth - 1) := by
  obtain ⟨fixedConstant, fixed_nonnegative, fixed_estimate⟩ := rootFibreData_kernel_residual_linearization data
  obtain ⟨parameterConstant, parameter_nonnegative, parameter_estimate⟩ := rootFibreData_parameter_taylor data
  obtain ⟨prefixConstant, prefix_nonnegative, prefix_estimate⟩ := rootFibreData_residual_derivative_shared_prefix data
  obtain ⟨minimumDepth, displacement_estimate⟩ := rootFibreData_root_displacement data
  let rootConstant := 4 * exponent / data.derivative_lower_bound
  have rootConstant_positive : 0 < rootConstant := by
    dsimp [rootConstant]
    exact div_pos (mul_pos (by norm_num) (by linarith [data.exponent_gt_one])) data.derivative_lower_bound_positive
  let errorConstant := fixedConstant + parameterConstant * rootConstant ^ 2 + prefixConstant * rootConstant
  have errorConstant_nonnegative : 0 ≤ errorConstant := by dsimp [errorConstant]; positivity
  refine ⟨errorConstant / data.derivative_lower_bound, div_nonneg errorConstant_nonnegative
    data.derivative_lower_bound_positive.le, minimumDepth, ?_⟩
  intro representative digits depth depth_ge agreement
  let ratio := data.root representative
  let displacement := data.root digits - ratio
  let derivative := deriv
    (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative) ratio
  let otherDerivative := deriv
    (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits) ratio
  let linearTerm := rootKernelLinearTerm data representative digits depth ratio
  let residual := cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits ratio
  have ratio_mem : ratio ∈ Set.Icc data.lower data.upper := data.root_in_band representative
  have ratio_positive : 0 < ratio := by linarith [data.lower_gt_quarter, ratio_mem.1]
  have ratio_lt_one : ratio < 1 := by linarith [data.upper_lt_half, ratio_mem.2]
  have displacement_bound : |displacement| ≤ rootConstant * ratio ^ depth := by
    simpa only [displacement, ratio, rootConstant, abs_sub_comm] using
      displacement_estimate digits representative depth depth_ge
        (fun index index_lt => (agreement index index_lt).symm)
  have representative_zero := (data.unique_root representative ratio ratio_mem).mpr rfl
  have digits_zero := (data.unique_root digits (data.root digits) (data.root_in_band digits)).mpr rfl
  have fixed_bound : |residual - linearTerm| ≤ fixedConstant * (ratio ^ depth) ^ 2 := by
    have bound := fixed_estimate representative digits depth ratio ratio_mem agreement
    rw [representative_zero, sub_zero] at bound
    exact bound
  have parameter_bound : |-residual - otherDerivative * displacement| ≤ parameterConstant * |displacement| ^ 2 := by
    have bound := parameter_estimate digits ratio (data.root digits) ratio_mem (data.root_in_band digits)
    rw [digits_zero, zero_sub] at bound
    exact bound
  have prefix_bound : |derivative - otherDerivative| ≤
      prefixConstant * ((depth : ℝ) + 1) * ratio ^ (depth - 1) :=
    prefix_estimate representative digits depth ratio ratio_mem agreement
  have numerator_bound : |derivative * displacement + linearTerm| ≤
      fixedConstant * (ratio ^ depth) ^ 2 + parameterConstant * |displacement| ^ 2 +
        |derivative - otherDerivative| * |displacement| := by
    rw [kernel_remainder_identity derivative otherDerivative displacement linearTerm residual]
    have triangle' : |-(-residual - otherDerivative * displacement) - (residual - linearTerm)| ≤
        |-residual - otherDerivative * displacement| + |residual - linearTerm| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (-(-residual - otherDerivative * displacement)) (-(residual - linearTerm))
    have triangle'' := abs_add_le
      (-(-residual - otherDerivative * displacement) - (residual - linearTerm))
      ((derivative - otherDerivative) * displacement)
    rw [abs_mul] at triangle''
    nlinarith [triangle', triangle'', fixed_bound, parameter_bound]
  have scale_bound : ratio ^ depth ≤ ratio ^ (depth - 1) :=
    pow_le_pow_of_le_one ratio_positive.le ratio_lt_one.le (by omega)
  have square_displacement := (sq_le_sq₀ (abs_nonneg displacement)
    (mul_nonneg rootConstant_positive.le (pow_nonneg ratio_positive.le depth))).mpr displacement_bound
  have product_bound := mul_le_mul prefix_bound displacement_bound (abs_nonneg displacement)
    (by positivity : 0 ≤ prefixConstant * ((depth : ℝ) + 1) * ratio ^ (depth - 1))
  have fixed_scale := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left scale_bound (pow_nonneg ratio_positive.le depth)) fixed_nonnegative
  have parameter_scale := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left scale_bound (pow_nonneg ratio_positive.le depth))
    (mul_nonneg parameter_nonnegative (sq_nonneg rootConstant))
  have scaled_numerator : |derivative * displacement + linearTerm| ≤
      errorConstant * ((depth : ℝ) + 1) * ratio ^ depth * ratio ^ (depth - 1) := by
    have parameter_square := mul_le_mul_of_nonneg_left square_displacement parameter_nonnegative
    have extra := mul_nonneg
      (mul_nonneg (add_nonneg fixed_nonnegative (mul_nonneg parameter_nonnegative (sq_nonneg rootConstant)))
        (Nat.cast_nonneg (α := ℝ) depth))
      (mul_nonneg (pow_nonneg ratio_positive.le depth) (pow_nonneg ratio_positive.le (depth - 1)))
    dsimp [errorConstant]
    nlinarith [numerator_bound, product_bound, fixed_scale, parameter_scale, parameter_square, extra]
  have derivative_lower : data.derivative_lower_bound ≤ |derivative| := data.transverse representative
  have derivative_nonzero : derivative ≠ 0 := by
    intro zero
    rw [zero, abs_zero] at derivative_lower
    linarith [data.derivative_lower_bound_positive]
  have kernel_identity : data.root digits - rootKernelValue data representative digits depth =
      (derivative * displacement + linearTerm) / derivative := by
    change data.root digits - (ratio - linearTerm / derivative) = _
    field_simp [derivative_nonzero]
    dsimp [displacement]
    ring
  rw [kernel_identity, abs_div]
  have division_bound := div_le_div_of_nonneg_left (abs_nonneg (derivative * displacement + linearTerm))
    data.derivative_lower_bound_positive derivative_lower
  have powers : depth + (depth - 1) = 2 * depth - 1 := by omega
  have final_scale : ratio ^ depth * ratio ^ (depth - 1) = ratio ^ (2 * depth - 1) := by
    rw [← pow_add, powers]
  calc
    _ ≤ |derivative * displacement + linearTerm| / data.derivative_lower_bound := division_bound
    _ ≤ (errorConstant * ((depth : ℝ) + 1) * ratio ^ depth * ratio ^ (depth - 1)) /
        data.derivative_lower_bound := div_le_div_of_nonneg_right scaled_numerator data.derivative_lower_bound_positive.le
    _ = _ := by
      rw [mul_assoc (errorConstant * ((depth : ℝ) + 1)), final_scale]
      dsimp [ratio]
      ring

end LambdaCantor.First.Roots
