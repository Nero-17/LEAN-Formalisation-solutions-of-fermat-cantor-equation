import LambdaCantor.First.AddressParameter

noncomputable section
namespace LambdaCantor

theorem summable_address_second_derivative_majorant {upper : ℝ}
    (positive : 0 < upper) (less_one : upper < 1) :
    Summable (fun index : ℕ => ((index : ℝ) + 1) * index * upper ^ (index - 1)) := by
  have norm_lt : ‖upper‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos positive]
  have quadratic := summable_pow_mul_geometric_of_norm_lt_one 2 norm_lt
  have linear := summable_pow_mul_geometric_of_norm_lt_one 1 norm_lt
  convert! (quadratic.add linear).mul_right upper⁻¹ using 1
  funext index
  cases index with
  | zero => simp
  | succ index =>
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_one, pow_succ]
      field_simp [positive.ne']
      <;> ring

private theorem weighted_digits_summable {weights : ℕ → ℝ}
    (nonnegative : ∀ index, 0 ≤ weights index) (summable : Summable weights)
    (digits : ℕ → Bool) :
    Summable (fun index => (if digits index then (1 : ℝ) else 0) * weights index) := by
  apply Summable.of_nonneg_of_le (f := weights)
  · intro index; split_ifs <;> simp [nonnegative index]
  · intro index; split_ifs <;> simp [nonnegative index]
  · exact summable

theorem hasDerivAt_address_derivative_series {ratio upper : ℝ}
    (positive : 0 < ratio) (below_upper : ratio < upper) (less_one : upper < 1)
    (digits : ℕ → Bool) :
    HasDerivAt
      (fun parameter => ∑' index : ℕ,
        (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * parameter ^ index)
      (∑' index : ℕ, (if digits (index + 1) then (1 : ℝ) else 0) *
        ((index : ℝ) + 1) * index * ratio ^ (index - 1)) ratio := by
  have upper_positive := positive.trans below_upper
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun index : ℕ => ((index : ℝ) + 1) * index * upper ^ (index - 1))
    (g := fun index parameter => (if digits (index + 1) then (1 : ℝ) else 0) *
      ((index : ℝ) + 1) * parameter ^ index)
    (g' := fun index parameter => (if digits (index + 1) then (1 : ℝ) else 0) *
      ((index : ℝ) + 1) * index * parameter ^ (index - 1))
    (t := Set.Ioo (0 : ℝ) upper) (y₀ := ratio) (y := ratio)
    (summable_address_second_derivative_majorant upper_positive less_one)
    isOpen_Ioo isPreconnected_Ioo
  · intro index parameter hparameter
    simpa only [mul_assoc, mul_one] using!
      ((hasDerivAt_id parameter).pow index).const_mul
        ((if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1))
  · intro index parameter hparameter
    split_ifs
    · simp only [one_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg index)) (pow_nonneg hparameter.1.le _))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hparameter.1.le hparameter.2.le _) (by positivity)
    · simp only [zero_mul, norm_zero]; positivity
  · exact ⟨positive, below_upper⟩
  · simpa only [mul_assoc] using weighted_digits_summable
      (fun index => mul_nonneg (by positivity) (pow_nonneg positive.le index))
      (summable_address_derivative_majorant positive.le (below_upper.trans less_one))
      (fun index => digits (index + 1))
  · exact ⟨positive, below_upper⟩

def addressParameterSecondDerivative (ratio : ℝ) (digits : ℕ → Bool) : ℝ :=
  -2 * (∑' index : ℕ,
    (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index) +
  (1 - ratio) * (∑' index : ℕ, (if digits (index + 1) then (1 : ℝ) else 0) *
    ((index : ℝ) + 1) * index * ratio ^ (index - 1))

theorem hasDerivAt_addressParameterDerivative {ratio : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1) (digits : ℕ → Bool) :
    HasDerivAt (fun parameter => addressParameterDerivative parameter digits)
      (addressParameterSecondDerivative ratio digits) ratio := by
  have below_upper : ratio < (ratio + 1) / 2 := by linarith
  have upper_lt : (ratio + 1) / 2 < 1 := by linarith
  have first_series : HasDerivAt
      (fun parameter => ∑' index : ℕ,
        (if digits index then (1 : ℝ) else 0) * parameter ^ index)
      (∑' index : ℕ,
        (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index)
      ratio := by
    apply ((hasDerivAt_address_series_tail positive below_upper upper_lt digits).const_add
      (if digits 0 then (1 : ℝ) else 0)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Set.Ioo (0 : ℝ) 1 from
      ⟨positive, less_one⟩)] with parameter hparameter
    exact (address_series_split hparameter.1.le hparameter.2 digits).symm
  have second_series := hasDerivAt_address_derivative_series positive below_upper upper_lt digits
  convert! first_series.neg.add (((hasDerivAt_id ratio).const_sub 1).mul second_series) using 1
    <;> dsimp [addressParameterDerivative, addressParameterSecondDerivative]
    <;> ring

def addressParameterSecondDerivativeBound (upper : ℝ) : ℝ :=
  2 * (∑' index : ℕ, ((index : ℝ) + 1) * upper ^ index) +
    ∑' index : ℕ, ((index : ℝ) + 1) * index * upper ^ (index - 1)

theorem address_parameter_second_derivative_bound {ratio upper : ℝ}
    (nonnegative : 0 ≤ ratio) (below_upper : ratio ≤ upper) (upper_positive : 0 < upper)
    (less_one : upper < 1) (digits : ℕ → Bool) :
    |addressParameterSecondDerivative ratio digits| ≤ addressParameterSecondDerivativeBound upper := by
  have first_nonnegative : ∀ index : ℕ, 0 ≤
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index := by
    intro index; split_ifs <;> positivity
  have first_le : ∀ index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index ≤
        ((index : ℝ) + 1) * upper ^ index := by
    intro index
    split_ifs
    · simp only [one_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonnegative below_upper _) (by positivity)
    · simp only [zero_mul]; positivity
  have second_nonnegative : ∀ index : ℕ, 0 ≤
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * index * ratio ^ (index - 1) := by
    intro index; split_ifs <;> positivity
  have second_le : ∀ index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * index * ratio ^ (index - 1) ≤
        ((index : ℝ) + 1) * index * upper ^ (index - 1) := by
    intro index
    split_ifs
    · simp only [one_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonnegative below_upper _) (by positivity)
    · simp only [zero_mul]; positivity
  have first_summable := Summable.of_nonneg_of_le first_nonnegative first_le
    (summable_address_derivative_majorant upper_positive.le less_one)
  have second_summable := Summable.of_nonneg_of_le second_nonnegative second_le
    (summable_address_second_derivative_majorant upper_positive less_one)
  have first_sum_nonnegative : 0 ≤ (∑' index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index) :=
    tsum_nonneg first_nonnegative
  have second_sum_nonnegative : 0 ≤ (∑' index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * index * ratio ^ (index - 1)) :=
    tsum_nonneg second_nonnegative
  have first_sum_le := first_summable.tsum_le_tsum first_le
    (summable_address_derivative_majorant upper_positive.le less_one)
  have second_sum_le := second_summable.tsum_le_tsum second_le
    (summable_address_second_derivative_majorant upper_positive less_one)
  have complement_nonnegative : 0 ≤ 1 - ratio := by linarith
  unfold addressParameterSecondDerivative addressParameterSecondDerivativeBound
  calc
    _ ≤ 2 * (∑' index : ℕ,
        (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index) +
      (1 - ratio) * (∑' index : ℕ, (if digits (index + 1) then (1 : ℝ) else 0) *
        ((index : ℝ) + 1) * index * ratio ^ (index - 1)) := by
      simpa only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg first_sum_nonnegative, abs_of_nonneg second_sum_nonnegative,
        abs_of_nonneg complement_nonnegative] using abs_add_le
          (-2 * (∑' index : ℕ,
            (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index))
          ((1 - ratio) * (∑' index : ℕ, (if digits (index + 1) then (1 : ℝ) else 0) *
            ((index : ℝ) + 1) * index * ratio ^ (index - 1)))
    _ ≤ _ := by nlinarith

theorem address_parameter_derivative_lipschitz_estimate {lower upper left right : ℝ}
    (lower_positive : 0 < lower) (upper_lt_one : upper < 1)
    (left_mem : left ∈ Set.Icc lower upper) (right_mem : right ∈ Set.Icc lower upper)
    (digits : ℕ → Bool) :
    |addressParameterDerivative right digits - addressParameterDerivative left digits| ≤
      addressParameterSecondDerivativeBound upper * |right - left| := by
  have upper_positive : 0 < upper := lower_positive.trans_le (left_mem.1.trans left_mem.2)
  have differentiable : ∀ parameter ∈ Set.Icc lower upper,
      DifferentiableAt ℝ (fun parameter => addressParameterDerivative parameter digits) parameter := by
    intro parameter hparameter
    exact (hasDerivAt_addressParameterDerivative (lower_positive.trans_le hparameter.1)
      (hparameter.2.trans_lt upper_lt_one) digits).differentiableAt
  have bound : ∀ parameter ∈ Set.Icc lower upper,
      ‖deriv (fun parameter => addressParameterDerivative parameter digits) parameter‖ ≤
        addressParameterSecondDerivativeBound upper := by
    intro parameter hparameter
    rw [(hasDerivAt_addressParameterDerivative (lower_positive.trans_le hparameter.1)
      (hparameter.2.trans_lt upper_lt_one) digits).deriv, Real.norm_eq_abs]
    exact address_parameter_second_derivative_bound (lower_positive.le.trans hparameter.1)
      hparameter.2 upper_positive upper_lt_one digits
  simpa only [Real.norm_eq_abs] using
    (convex_Icc lower upper).norm_image_sub_le_of_norm_deriv_le differentiable bound left_mem right_mem

end LambdaCantor

