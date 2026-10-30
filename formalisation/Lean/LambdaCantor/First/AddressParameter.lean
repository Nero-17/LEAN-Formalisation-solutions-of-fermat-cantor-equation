import LambdaCantor.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import LambdaCantor.First.Library.SmoothSeries

noncomputable section
namespace LambdaCantor

/-- A summable derivative majorant, independent of the binary address. -/
theorem summable_address_derivative_majorant {upper : ℝ}
    (hupper_nonneg : 0 ≤ upper) (hupper_lt : upper < 1) :
    Summable (fun index : ℕ => ((index : ℝ) + 1) * upper ^ index) := by
  have hnorm : ‖upper‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hupper_nonneg]
  have hlinear := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hconstant := summable_geometric_of_lt_one hupper_nonneg hupper_lt
  simpa only [pow_one, add_mul, one_mul] using hlinear.add hconstant

/-- Parameter differentiation of the nonconstant part of the digit series. -/
theorem hasDerivAt_address_series_tail {ratio upper : ℝ}
    (hratio : 0 < ratio) (hratio_upper : ratio < upper) (hupper : upper < 1)
    (digits : ℕ → Bool) :
    HasDerivAt
      (fun parameter => ∑' index : ℕ,
        (if digits (index + 1) then (1 : ℝ) else 0) * parameter ^ (index + 1))
      (∑' index : ℕ,
        (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index)
      ratio := by
  have hupper_pos : 0 < upper := lt_trans hratio hratio_upper
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun index : ℕ => ((index : ℝ) + 1) * upper ^ index)
    (g := fun index parameter => (if digits (index + 1) then (1 : ℝ) else 0) * parameter ^ (index + 1))
    (g' := fun index parameter => (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * parameter ^ index)
    (t := Set.Ioo (0 : ℝ) upper) (y₀ := ratio) (y := ratio)
    (summable_address_derivative_majorant hupper_pos.le hupper)
    isOpen_Ioo isPreconnected_Ioo
  · intro index parameter hparameter
    simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using! ((hasDerivAt_id parameter).pow (index + 1)).const_mul (if digits (index + 1) then (1 : ℝ) else 0)
  · intro index parameter hparameter
    split_ifs
    · simp only [one_mul]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hparameter.1.le _))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hparameter.1.le hparameter.2.le index) (by positivity)
    · simp only [zero_mul, norm_zero]
      positivity
  · exact ⟨hratio, hratio_upper⟩
  · exact (address_summable hratio.le (lt_trans hratio_upper hupper) digits).comp_injective
      (fun _ _ equality => Nat.add_right_cancel equality)
  · exact ⟨hratio, hratio_upper⟩



/-- The constant digit split, stated for parameter differentiation. -/
theorem address_series_split {ratio : ℝ} (hnonneg : 0 ≤ ratio) (hlt : ratio < 1)
    (digits : ℕ → Bool) :
    (if digits 0 then (1 : ℝ) else 0) +
      (∑' index : ℕ, (if digits (index + 1) then (1 : ℝ) else 0) * ratio ^ (index + 1)) =
      ∑' index : ℕ, (if digits index then (1 : ℝ) else 0) * ratio ^ index := by
  simpa using (address_summable hnonneg hlt digits).sum_add_tsum_nat_add 1

/-- The actual parameter derivative of the paper's address map. -/
def addressParameterDerivative (ratio : ℝ) (digits : ℕ → Bool) : ℝ :=
  -(∑' index : ℕ, (if digits index then (1 : ℝ) else 0) * ratio ^ index) +
    (1 - ratio) * (∑' index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index)

/-- Every address is differentiable in the contraction parameter on (0,1). -/
theorem hasDerivAt_address_parameter {ratio : ℝ} (hratio : 0 < ratio) (hlt : ratio < 1)
    (digits : ℕ → Bool) :
    HasDerivAt (fun parameter => address parameter digits)
      (addressParameterDerivative ratio digits) ratio := by
  have hupper : ratio < (ratio + 1) / 2 := by linarith
  have hupper_lt : (ratio + 1) / 2 < 1 := by linarith
  have htail := hasDerivAt_address_series_tail hratio hupper hupper_lt digits
  have hproduct := ((hasDerivAt_id ratio).const_sub 1).mul
    (htail.const_add (if digits 0 then (1 : ℝ) else 0))
  have hproduct' : HasDerivAt
      (fun parameter => (1 - parameter) * ((if digits 0 then (1 : ℝ) else 0) +
        ∑' index : ℕ, (if digits (index + 1) then (1 : ℝ) else 0) * parameter ^ (index + 1)))
      (addressParameterDerivative ratio digits) ratio := by
    simpa only [addressParameterDerivative, Pi.mul_apply, id_eq, neg_mul, one_mul, address_series_split hratio.le hlt]
      using! hproduct
  apply hproduct'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show ratio ∈ Set.Ioo (0 : ℝ) 1 from ⟨hratio, hlt⟩)]
    with parameter hparameter
  dsimp [address]
  rw [address_series_split hparameter.1.le hparameter.2]





/-- A finite parameter-derivative bound shared by every binary address. -/
def addressParameterDerivativeBound (upper : ℝ) : ℝ :=
  (1 - upper)⁻¹ + ∑' index : ℕ, ((index : ℝ) + 1) * upper ^ index

theorem address_parameter_derivative_bound {ratio upper : ℝ}
    (hratio : 0 ≤ ratio) (hratio_upper : ratio ≤ upper) (hupper : upper < 1)
    (digits : ℕ → Bool) :
    |addressParameterDerivative ratio digits| ≤ addressParameterDerivativeBound upper := by
  have hupper_nonneg : 0 ≤ upper := le_trans hratio hratio_upper
  have hratio_lt : ratio < 1 := lt_of_le_of_lt hratio_upper hupper
  have hterm : ∀ index : ℕ,
      (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index ≤
        ((index : ℝ) + 1) * upper ^ index := by
    intro index
    split_ifs
    · simp only [one_mul]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hratio hratio_upper index) (by positivity)
    · simp only [zero_mul]
      positivity
  have hderivative_nonneg : ∀ index : ℕ,
      0 ≤ (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index := by
    intro index
    split_ifs <;> positivity
  have hderivative_summable := Summable.of_nonneg_of_le hderivative_nonneg hterm
    (summable_address_derivative_majorant hupper_nonneg hupper)
  have hderivative_sum_bound := hderivative_summable.tsum_le_tsum hterm
    (summable_address_derivative_majorant hupper_nonneg hupper)
  have hderivative_sum_nonneg : 0 ≤ ∑' index : ℕ, (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index := tsum_nonneg hderivative_nonneg
  have hseries_nonneg : 0 ≤ ∑' index : ℕ,
      (if digits index then (1 : ℝ) else 0) * ratio ^ index := by
    apply tsum_nonneg
    intro index
    split_ifs <;> positivity
  have hseries_bound := (address_summable hratio hratio_lt digits).tsum_le_tsum
    (fun index => show (if digits index then (1 : ℝ) else 0) * ratio ^ index ≤ upper ^ index by
      split_ifs
      · simpa using pow_le_pow_left₀ hratio hratio_upper index
      · simp [pow_nonneg hupper_nonneg])
    (summable_geometric_of_lt_one hupper_nonneg hupper)
  rw [tsum_geometric_of_lt_one hupper_nonneg hupper] at hseries_bound
  unfold addressParameterDerivative addressParameterDerivativeBound
  calc
    _ ≤ (∑' index : ℕ, (if digits index then (1 : ℝ) else 0) * ratio ^ index) +
        (1 - ratio) * (∑' index : ℕ,
          (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index) := by
      simpa only [abs_neg, abs_of_nonneg hseries_nonneg,
        abs_of_nonneg (mul_nonneg (by linarith : 0 ≤ 1 - ratio) hderivative_sum_nonneg)]
        using abs_add_le
          (-(∑' index : ℕ, (if digits index then (1 : ℝ) else 0) * ratio ^ index))
          ((1 - ratio) * (∑' index : ℕ,
            (if digits (index + 1) then (1 : ℝ) else 0) * ((index : ℝ) + 1) * ratio ^ index))
    _ ≤ _ := by nlinarith




/-- Uniform Lipschitz control in the parameter, independent of the address. -/
theorem address_parameter_lipschitz_estimate {lower upper left right : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1)
    (hleft : left ∈ Set.Icc lower upper) (hright : right ∈ Set.Icc lower upper)
    (digits : ℕ → Bool) :
    |address right digits - address left digits| ≤
      addressParameterDerivativeBound upper * |right - left| := by
  have hdifferentiable : ∀ parameter ∈ Set.Icc lower upper,
      DifferentiableAt ℝ (fun parameter => address parameter digits) parameter := by
    intro parameter hparameter
    exact (hasDerivAt_address_parameter (lt_of_lt_of_le hlower hparameter.1)
      (lt_of_le_of_lt hparameter.2 hupper) digits).differentiableAt
  have hbound : ∀ parameter ∈ Set.Icc lower upper,
      ‖deriv (fun parameter => address parameter digits) parameter‖ ≤
        addressParameterDerivativeBound upper := by
    intro parameter hparameter
    rw [(hasDerivAt_address_parameter (lt_of_lt_of_le hlower hparameter.1)
      (lt_of_le_of_lt hparameter.2 hupper) digits).deriv, Real.norm_eq_abs]
    exact address_parameter_derivative_bound
      (le_trans hlower.le hparameter.1) hparameter.2 hupper digits
  simpa only [Real.norm_eq_abs] using
    (convex_Icc lower upper).norm_image_sub_le_of_norm_deriv_le
      hdifferentiable hbound hleft hright

end LambdaCantor

