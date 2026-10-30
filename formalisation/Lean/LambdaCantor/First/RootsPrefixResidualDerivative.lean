import LambdaCantor.First.RootsResidualDerivativeBounds

noncomputable section
namespace LambdaCantor.First.Roots

theorem rootFibreData_residual_derivative_shared_prefix {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (left right : ℕ → Bool × Bool) (depth : ℕ) (ratio : ℝ),
      ratio ∈ Set.Icc data.lower data.upper → (∀ index < depth, left index = right index) →
      |deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength left) ratio -
        deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength right) ratio| ≤
        constant * ((depth : ℝ) + 1) * ratio ^ (depth - 1) := by
  obtain ⟨lowerCoordinate, lower_positive, coordinate_lower⟩ := rootFibreData_uniform_positive_coordinates data
  let powerConstant : ℝ := |exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2))
  let derivativeBound := addressParameterDerivativeBound data.upper
  let constant : ℝ := exponent * ((data.leftLength : ℝ) + (data.rightLength : ℝ) + 2 +
    4 * derivativeBound + 2 * derivativeBound * powerConstant)
  refine ⟨max 0 constant, le_max_left _ _, ?_⟩
  intro left right depth ratio in_band agreement
  have ratio_positive : 0 < ratio := by linarith [data.lower_gt_quarter, in_band.1]
  have upper_lt_one : data.upper < 1 := by linarith [data.upper_lt_half]
  have ratio_lt_one := in_band.2.trans_lt upper_lt_one
  have powerConstant_nonnegative : 0 ≤ powerConstant := by dsimp [powerConstant]; positivity
  have derivativeBound_nonnegative : 0 ≤ derivativeBound :=
    (abs_nonneg _).trans (address_parameter_derivative_bound ratio_positive.le in_band.2 upper_lt_one (fun _ => false))
  have coordinate_bound (word : ℕ → Bool) (length : ℕ) (coordinate : Bool × Bool → Bool)
      (left_lower : lowerCoordinate ≤ cylinderCoordinate word length (fun index => coordinate (left index)) ratio)
      (right_lower : lowerCoordinate ≤ cylinderCoordinate word length (fun index => coordinate (right index)) ratio) :
      |deriv (cylinderCoordinate word length (fun index => coordinate (left index))) ratio * exponent *
          cylinderCoordinate word length (fun index => coordinate (left index)) ratio ^ (exponent - 1) -
        deriv (cylinderCoordinate word length (fun index => coordinate (right index))) ratio * exponent *
          cylinderCoordinate word length (fun index => coordinate (right index)) ratio ^ (exponent - 1)| ≤
        exponent * ((length : ℝ) + 1 + 2 * derivativeBound + derivativeBound * powerConstant) *
          ((depth : ℝ) + 1) * ratio ^ (depth - 1) := by
    have product_bound := power_derivative_product_difference
      (firstSlope := deriv (cylinderCoordinate word length (fun index => coordinate (left index))) ratio)
      (secondSlope := deriv (cylinderCoordinate word length (fun index => coordinate (right index))) ratio)
      data.exponent_gt_one lower_positive
      ⟨left_lower, (cylinderCoordinate_in_unit_interval ratio_positive.le ratio_lt_one word length _).2⟩
      ⟨right_lower, (cylinderCoordinate_in_unit_interval ratio_positive.le ratio_lt_one word length _).2⟩
      (cylinderCoordinate_derivative_bound ratio_positive in_band.2 upper_lt_one word length
        (fun index => coordinate (right index)))
    have derivative_bound := cylinderCoordinate_shared_prefix_derivative_bound ratio_positive in_band.2 upper_lt_one
      word length depth (fun index => coordinate (left index)) (fun index => coordinate (right index))
      (fun index index_lt => congrArg coordinate (agreement index index_lt))
    have coordinate_difference := cylinderCoordinate_shared_prefix_bound ratio_positive.le ratio_lt_one word length depth
      (fun index => coordinate (left index)) (fun index => coordinate (right index))
      (fun index index_lt => congrArg coordinate (agreement index index_lt))
    have power_one : ratio ^ (length + depth - 1) ≤ ratio ^ (depth - 1) :=
      pow_le_pow_of_le_one ratio_positive.le ratio_lt_one.le (by omega)
    have power_two : ratio ^ (length + depth) ≤ ratio ^ (depth - 1) :=
      pow_le_pow_of_le_one ratio_positive.le ratio_lt_one.le (by omega)
    have coordinate_scale : ratio ^ length * ratio ^ depth ≤ ratio ^ (depth - 1) := by
      rw [← pow_add]
      exact power_two
    have derivative_bound' : |deriv (cylinderCoordinate word length (fun index => coordinate (left index))) ratio -
        deriv (cylinderCoordinate word length (fun index => coordinate (right index))) ratio| ≤
        (((length + depth : ℕ) : ℝ) + 2 * derivativeBound) * ratio ^ (depth - 1) := by
      have first := mul_le_mul_of_nonneg_left power_one (Nat.cast_nonneg (α := ℝ) (length + depth))
      have second : (2 * derivativeBound) * ratio ^ (length + depth) ≤
          (2 * derivativeBound) * ratio ^ (depth - 1) :=
        mul_le_mul_of_nonneg_left power_two
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) derivativeBound_nonnegative)
      exact derivative_bound.trans (by dsimp [derivativeBound] at *; nlinarith [first, second])
    have coordinate_bound' := mul_le_mul_of_nonneg_left (coordinate_difference.trans coordinate_scale)
      (mul_nonneg derivativeBound_nonnegative powerConstant_nonnegative)
    have sum_bound := add_le_add derivative_bound' coordinate_bound'
    have weighted_bound := mul_le_mul_of_nonneg_left sum_bound
      (show 0 ≤ exponent by linarith [data.exponent_gt_one])
    have depth_nonnegative := Nat.cast_nonneg (α := ℝ) depth
    have length_nonnegative := Nat.cast_nonneg (α := ℝ) length
    have extra_nonnegative : 0 ≤ (length : ℝ) * depth +
        (2 * derivativeBound + derivativeBound * powerConstant) * depth := by positivity
    have scale_nonnegative := pow_nonneg ratio_positive.le (depth - 1)
    have coefficient_bound : (((length + depth : ℕ) : ℝ) + 2 * derivativeBound) +
        derivativeBound * powerConstant ≤
        ((length : ℝ) + 1 + 2 * derivativeBound + derivativeBound * powerConstant) *
          ((depth : ℝ) + 1) := by
      rw [Nat.cast_add]
      nlinarith [extra_nonnegative]
    have factor_bound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left coefficient_bound
        (show 0 ≤ exponent by linarith [data.exponent_gt_one])) scale_nonnegative
    apply product_bound.trans
    apply weighted_bound.trans
    calc
      _ = exponent * ((((length + depth : ℕ) : ℝ) + 2 * derivativeBound) +
          derivativeBound * powerConstant) * ratio ^ (depth - 1) := by ring
      _ ≤ exponent *
          (((length : ℝ) + 1 + 2 * derivativeBound + derivativeBound * powerConstant) *
            ((depth : ℝ) + 1)) * ratio ^ (depth - 1) := factor_bound
      _ = _ := by ring
  have left_bound := coordinate_bound data.leftWord data.leftLength Prod.fst
    (coordinate_lower left ratio in_band).1 (coordinate_lower right ratio in_band).1
  have right_bound := coordinate_bound data.rightWord data.rightLength Prod.snd
    (coordinate_lower left ratio in_band).2 (coordinate_lower right ratio in_band).2
  rw [(hasDerivAt_cylinderResidual ratio_positive ratio_lt_one data.exponent_gt_one.le _ _ _ _ _).deriv,
    (hasDerivAt_cylinderResidual ratio_positive ratio_lt_one data.exponent_gt_one.le _ _ _ _ _).deriv]
  unfold cylinderResidualDerivative
  simp_rw [← (hasDerivAt_cylinderCoordinate ratio_positive ratio_lt_one _ _ _).deriv]
  have identity : ∀ a b c d : ℝ, (a + b) - (c + d) = (a - c) + (b - d) := by intros; ring
  rw [identity]
  have sum_bound := (abs_add_le _ _).trans (add_le_add left_bound right_bound)
  have max_bound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right (0 : ℝ) constant) (by positivity : 0 ≤ (depth : ℝ) + 1))
    (pow_nonneg ratio_positive.le (depth - 1))
  dsimp [constant] at max_bound
  nlinarith [sum_bound, max_bound]

end LambdaCantor.First.Roots
