import LambdaCantor.Addresses
import LambdaCantor.First.AddressParameter

noncomputable section
namespace LambdaCantor

/-- Shared prefixes cancel exactly, leaving only scaled tail differences. -/
theorem address_shared_prefix_difference {ratio : ℝ} (hnonneg : 0 ≤ ratio) (hlt : ratio < 1)
    (left right : ℕ → Bool) (length : ℕ)
    (hagreement : ∀ index < length, left index = right index) :
    address ratio left - address ratio right = ratio ^ length *
      (address ratio (fun index => left (index + length)) -
       address ratio (fun index => right (index + length))) := by
  have hprefix : prefixValue ratio left length = prefixValue ratio right length := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro index hindex
    rw [hagreement index (Finset.mem_range.mp hindex)]
  rw [address_prefix_tail hnonneg hlt left length,
    address_prefix_tail hnonneg hlt right length, hprefix]
  ring

/-- Uniform scale of address variation within a fixed cylinder. -/
theorem address_shared_prefix_bound {ratio : ℝ} (hnonneg : 0 ≤ ratio) (hlt : ratio < 1)
    (left right : ℕ → Bool) (length : ℕ)
    (hagreement : ∀ index < length, left index = right index) :
    |address ratio left - address ratio right| ≤ ratio ^ length := by
  rw [address_shared_prefix_difference hnonneg hlt left right length hagreement,
    abs_mul, abs_of_nonneg (pow_nonneg hnonneg length)]
  have htail : |address ratio (fun index => left (index + length)) -
      address ratio (fun index => right (index + length))| ≤ 1 := by
    apply abs_le.mpr
    have hleft_nonneg := address_nonnegative hnonneg hlt (fun index => left (index + length))
    have hleft_le := address_le_one hnonneg hlt (fun index => left (index + length))
    have hright_nonneg := address_nonnegative hnonneg hlt (fun index => right (index + length))
    have hright_le := address_le_one hnonneg hlt (fun index => right (index + length))
    constructor <;> linarith
  simpa using mul_le_mul_of_nonneg_left htail (pow_nonneg hnonneg length)

/-- Exact parameter derivative of a shared-prefix difference. -/
theorem address_shared_prefix_derivative {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1)
    (left right : ℕ → Bool) (length : ℕ)
    (hagreement : ∀ index < length, left index = right index) :
    addressParameterDerivative ratio left - addressParameterDerivative ratio right =
      (length : ℝ) * ratio ^ (length - 1) *
        (address ratio (fun index => left (index + length)) -
         address ratio (fun index => right (index + length))) +
      ratio ^ length *
        (addressParameterDerivative ratio (fun index => left (index + length)) -
         addressParameterDerivative ratio (fun index => right (index + length))) := by
  have hactual := (hasDerivAt_address_parameter hpos hlt left).sub
    (hasDerivAt_address_parameter hpos hlt right)
  have htail := (hasDerivAt_address_parameter hpos hlt (fun index => left (index + length))).sub
    (hasDerivAt_address_parameter hpos hlt (fun index => right (index + length)))
  have hscaled := ((hasDerivAt_id ratio).pow length).mul htail
  have hscaled_actual := hscaled.congr_of_eventuallyEq
    (show (fun parameter => address parameter left - address parameter right) =ᶠ[nhds ratio]
      (fun parameter => parameter ^ length *
        (address parameter (fun index => left (index + length)) -
         address parameter (fun index => right (index + length)))) from by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show ratio ∈ Set.Ioo (0 : ℝ) 1 from ⟨hpos, hlt⟩)] with parameter hparameter
      exact address_shared_prefix_difference hparameter.1.le hparameter.2 left right length hagreement)
  simpa using hactual.unique hscaled_actual



/-- The explicit derivative error scale used in the frozen-kernel replacement
argument: a shared length-j prefix gives j*ratio^(j-1)+O(ratio^j). -/
theorem address_shared_prefix_derivative_bound {ratio upper : ℝ}
    (hpos : 0 < ratio) (hratio_upper : ratio ≤ upper) (hupper : upper < 1)
    (left right : ℕ → Bool) (length : ℕ)
    (hagreement : ∀ index < length, left index = right index) :
    |addressParameterDerivative ratio left - addressParameterDerivative ratio right| ≤
      (length : ℝ) * ratio ^ (length - 1) +
        2 * addressParameterDerivativeBound upper * ratio ^ length := by
  have hlt : ratio < 1 := lt_of_le_of_lt hratio_upper hupper
  have htail : |address ratio (fun index => left (index + length)) -
      address ratio (fun index => right (index + length))| ≤ 1 := by
    simpa using address_shared_prefix_bound hpos.le hlt
      (fun index => left (index + length)) (fun index => right (index + length)) 0
      (by intro index hindex; omega)
  have htail_derivative :
      |addressParameterDerivative ratio (fun index => left (index + length)) -
       addressParameterDerivative ratio (fun index => right (index + length))| ≤
        2 * addressParameterDerivativeBound upper := by
    calc
      _ ≤ |addressParameterDerivative ratio (fun index => left (index + length))| +
          |addressParameterDerivative ratio (fun index => right (index + length))| := abs_sub _ _
      _ ≤ _ := by
        have hleft := address_parameter_derivative_bound hpos.le hratio_upper hupper
          (fun index => left (index + length))
        have hright := address_parameter_derivative_bound hpos.le hratio_upper hupper
          (fun index => right (index + length))
        linarith
  rw [address_shared_prefix_derivative hpos hlt left right length hagreement]
  calc
    _ ≤ |(length : ℝ) * ratio ^ (length - 1) *
        (address ratio (fun index => left (index + length)) -
         address ratio (fun index => right (index + length)))| +
      |ratio ^ length *
        (addressParameterDerivative ratio (fun index => left (index + length)) -
         addressParameterDerivative ratio (fun index => right (index + length)))| := abs_add_le _ _
    _ ≤ (length : ℝ) * ratio ^ (length - 1) * 1 +
        ratio ^ length * (2 * addressParameterDerivativeBound upper) := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (length : ℝ) from Nat.cast_nonneg length),
        abs_of_nonneg (pow_nonneg hpos.le (length - 1)),
        abs_of_nonneg (pow_nonneg hpos.le length)]
      exact add_le_add
        (mul_le_mul_of_nonneg_left htail (by positivity))
        (mul_le_mul_of_nonneg_left htail_derivative (by positivity))
    _ = _ := by ring

end LambdaCantor

