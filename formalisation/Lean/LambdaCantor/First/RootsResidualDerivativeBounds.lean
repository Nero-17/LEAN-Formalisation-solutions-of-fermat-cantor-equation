import LambdaCantor.First.RootsCylinderDifferences
import LambdaCantor.First.RootsCoordinateBounds

noncomputable section
namespace LambdaCantor.First.Roots

theorem power_derivative_product_difference {exponent lowerCoordinate first second firstSlope secondSlope bound : ℝ}
    (exponent_gt_one : 1 < exponent) (lower_positive : 0 < lowerCoordinate)
    (first_mem : first ∈ Set.Icc lowerCoordinate 1) (second_mem : second ∈ Set.Icc lowerCoordinate 1)
    (slope_bound : |secondSlope| ≤ bound) :
    |firstSlope * exponent * first ^ (exponent - 1) - secondSlope * exponent * second ^ (exponent - 1)| ≤
      exponent * (|firstSlope - secondSlope| + bound *
        (|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2))) * |first - second|) := by
  have first_positive := lower_positive.trans_le first_mem.1
  have power_bound := Real.rpow_le_one first_positive.le first_mem.2
    (show 0 ≤ exponent - 1 by linarith)
  have power_difference := rpow_lipschitz_positive_band (exponent := exponent - 1)
    lower_positive first_mem second_mem
  have exponent_identity : exponent - 1 - 1 = exponent - 2 := by ring
  rw [exponent_identity] at power_difference
  have identity : firstSlope * exponent * first ^ (exponent - 1) -
      secondSlope * exponent * second ^ (exponent - 1) = exponent *
        ((firstSlope - secondSlope) * first ^ (exponent - 1) +
          secondSlope * (first ^ (exponent - 1) - second ^ (exponent - 1))) := by ring
  rw [identity, abs_mul, abs_of_pos (show 0 < exponent by linarith)]
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ exponent by linarith)
  calc
    _ ≤ |(firstSlope - secondSlope) * first ^ (exponent - 1)| +
        |secondSlope * (first ^ (exponent - 1) - second ^ (exponent - 1))| := abs_add_le _ _
    _ = |firstSlope - secondSlope| * first ^ (exponent - 1) +
        |secondSlope| * |first ^ (exponent - 1) - second ^ (exponent - 1)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg first_positive.le _)]
    _ ≤ |firstSlope - secondSlope| * 1 +
        bound * ((|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2))) * |first - second|) :=
      add_le_add (mul_le_mul_of_nonneg_left power_bound (abs_nonneg _))
        (mul_le_mul slope_bound power_difference (abs_nonneg _) ((abs_nonneg _).trans slope_bound))
    _ = _ := by ring

theorem cylinderCoordinate_in_unit_interval {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (word : ℕ → Bool) (length : ℕ) (digits : ℕ → Bool) :
    cylinderCoordinate word length digits ratio ∈ Set.Icc (0 : ℝ) 1 := by
  unfold cylinderCoordinate
  rw [← cylinder_address nonnegative less_one word length digits]
  exact ⟨address_nonnegative nonnegative less_one _, address_le_one nonnegative less_one _⟩

theorem cylinderCoordinate_derivative_bound {ratio upper : ℝ}
    (positive : 0 < ratio) (ratio_le_upper : ratio ≤ upper) (upper_lt_one : upper < 1)
    (word : ℕ → Bool) (length : ℕ) (digits : ℕ → Bool) :
    |deriv (cylinderCoordinate word length digits) ratio| ≤ addressParameterDerivativeBound upper := by
  rw [(hasDerivAt_cylinderCoordinate positive (ratio_le_upper.trans_lt upper_lt_one) word length digits).deriv]
  exact address_parameter_derivative_bound positive.le ratio_le_upper upper_lt_one _

theorem cylinderCoordinate_parameter_lipschitz {lower upper firstRatio secondRatio : ℝ}
    (lower_positive : 0 < lower) (upper_lt_one : upper < 1)
    (first_mem : firstRatio ∈ Set.Icc lower upper) (second_mem : secondRatio ∈ Set.Icc lower upper)
    (word : ℕ → Bool) (length : ℕ) (digits : ℕ → Bool) :
    |cylinderCoordinate word length digits firstRatio - cylinderCoordinate word length digits secondRatio| ≤
      addressParameterDerivativeBound upper * |firstRatio - secondRatio| := by
  unfold cylinderCoordinate
  rw [← cylinder_address (lower_positive.le.trans first_mem.1) (first_mem.2.trans_lt upper_lt_one),
    ← cylinder_address (lower_positive.le.trans second_mem.1) (second_mem.2.trans_lt upper_lt_one)]
  exact address_parameter_lipschitz_estimate lower_positive upper_lt_one second_mem first_mem _

theorem rootFibreData_residual_derivative_parameter_lipschitz {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (digits : ℕ → Bool × Bool) (firstRatio secondRatio : ℝ),
      firstRatio ∈ Set.Icc data.lower data.upper → secondRatio ∈ Set.Icc data.lower data.upper →
      |deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits) firstRatio -
        deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits) secondRatio| ≤
        constant * |firstRatio - secondRatio| := by
  obtain ⟨lowerCoordinate, lower_positive, coordinate_lower⟩ := rootFibreData_uniform_positive_coordinates data
  have lower_parameter_positive : 0 < data.lower := by linarith [data.lower_gt_quarter]
  have upper_lt_one : data.upper < 1 := by linarith [data.upper_lt_half]
  let constant : ℝ := 2 * exponent *
    (addressParameterSecondDerivativeBound data.upper + addressParameterDerivativeBound data.upper ^ 2 *
      (|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2))))
  refine ⟨max 0 constant, le_max_left _ _, ?_⟩
  intro digits firstRatio secondRatio first_mem second_mem
  have coordinate_bound (word : ℕ → Bool) (length : ℕ) (coordinate : Bool × Bool → Bool)
      (first_lower : lowerCoordinate ≤ cylinderCoordinate word length (fun index => coordinate (digits index)) firstRatio)
      (second_lower : lowerCoordinate ≤ cylinderCoordinate word length (fun index => coordinate (digits index)) secondRatio) :
      |deriv (cylinderCoordinate word length (fun index => coordinate (digits index))) firstRatio * exponent *
          cylinderCoordinate word length (fun index => coordinate (digits index)) firstRatio ^ (exponent - 1) -
        deriv (cylinderCoordinate word length (fun index => coordinate (digits index))) secondRatio * exponent *
          cylinderCoordinate word length (fun index => coordinate (digits index)) secondRatio ^ (exponent - 1)| ≤
      exponent * (addressParameterSecondDerivativeBound data.upper + addressParameterDerivativeBound data.upper ^ 2 *
        (|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2)))) * |firstRatio - secondRatio| := by
    have first_unit := cylinderCoordinate_in_unit_interval (lower_parameter_positive.le.trans first_mem.1)
      (first_mem.2.trans_lt upper_lt_one) word length (fun index => coordinate (digits index))
    have second_unit := cylinderCoordinate_in_unit_interval (lower_parameter_positive.le.trans second_mem.1)
      (second_mem.2.trans_lt upper_lt_one) word length (fun index => coordinate (digits index))
    have slope_bound := cylinderCoordinate_derivative_bound (lower_parameter_positive.trans_le second_mem.1)
      second_mem.2 upper_lt_one word length (fun index => coordinate (digits index))
    have product_bound := power_derivative_product_difference
      (firstSlope := deriv (cylinderCoordinate word length (fun index => coordinate (digits index))) firstRatio)
      (secondSlope := deriv (cylinderCoordinate word length (fun index => coordinate (digits index))) secondRatio)
      data.exponent_gt_one lower_positive
      ⟨first_lower, first_unit.2⟩ ⟨second_lower, second_unit.2⟩ slope_bound
    have coordinate_movement := cylinderCoordinate_parameter_lipschitz lower_parameter_positive upper_lt_one
      first_mem second_mem word length (fun index => coordinate (digits index))
    have derivative_movement := address_parameter_derivative_lipschitz_estimate lower_parameter_positive upper_lt_one
      second_mem first_mem (cylinderDigits word length (fun index => coordinate (digits index)))
    rw [← (hasDerivAt_cylinderCoordinate (lower_parameter_positive.trans_le first_mem.1)
        (first_mem.2.trans_lt upper_lt_one) word length (fun index => coordinate (digits index))).deriv,
      ← (hasDerivAt_cylinderCoordinate (lower_parameter_positive.trans_le second_mem.1)
        (second_mem.2.trans_lt upper_lt_one) word length (fun index => coordinate (digits index))).deriv] at derivative_movement
    have first_derivative_nonnegative : 0 ≤ addressParameterDerivativeBound data.upper :=
      (abs_nonneg _).trans slope_bound
    have power_constant_nonnegative : 0 ≤ |exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2)) := by positivity
    have scaled_movement := mul_le_mul_of_nonneg_left coordinate_movement
      (mul_nonneg first_derivative_nonnegative power_constant_nonnegative)
    have sum_bound := add_le_add derivative_movement scaled_movement
    have final_bound := mul_le_mul_of_nonneg_left sum_bound (show 0 ≤ exponent by linarith [data.exponent_gt_one])
    exact product_bound.trans (by nlinarith [final_bound])
  have left_bound := coordinate_bound data.leftWord data.leftLength Prod.fst
    (coordinate_lower digits firstRatio first_mem).1 (coordinate_lower digits secondRatio second_mem).1
  have right_bound := coordinate_bound data.rightWord data.rightLength Prod.snd
    (coordinate_lower digits firstRatio first_mem).2 (coordinate_lower digits secondRatio second_mem).2
  rw [(hasDerivAt_cylinderResidual (lower_parameter_positive.trans_le first_mem.1)
      (first_mem.2.trans_lt upper_lt_one) data.exponent_gt_one.le _ _ _ _ _).deriv,
    (hasDerivAt_cylinderResidual (lower_parameter_positive.trans_le second_mem.1)
      (second_mem.2.trans_lt upper_lt_one) data.exponent_gt_one.le _ _ _ _ _).deriv]
  unfold cylinderResidualDerivative
  simp_rw [← (hasDerivAt_cylinderCoordinate (lower_parameter_positive.trans_le first_mem.1)
      (first_mem.2.trans_lt upper_lt_one) _ _ _).deriv,
    ← (hasDerivAt_cylinderCoordinate (lower_parameter_positive.trans_le second_mem.1)
      (second_mem.2.trans_lt upper_lt_one) _ _ _).deriv]
  have identity : ∀ a b c d : ℝ, (a + b) - (c + d) = (a - c) + (b - d) := by intros; ring
  rw [identity]
  have sum_bound := (abs_add_le _ _).trans (add_le_add left_bound right_bound)
  have max_bound := mul_le_mul_of_nonneg_right (le_max_right (0 : ℝ) constant) (abs_nonneg (firstRatio - secondRatio))
  dsimp [constant] at max_bound
  nlinarith [sum_bound, max_bound]

end LambdaCantor.First.Roots
