import LambdaCantor.Last.ArithmeticField
import LambdaCantor.Addresses

noncomputable section
namespace LambdaCantor.Last

theorem prefixValue_mem_parameterField (ratio : ℝ) (digits : ℕ → Bool) (length : ℕ) :
    prefixValue ratio digits length ∈ parameterField ratio := by
  apply (parameterField ratio).mul_mem
  · exact (parameterField ratio).sub_mem (parameterField ratio).one_mem
      (ratio_mem_parameterField ratio)
  · apply (parameterField ratio).sum_mem
    intro index _
    apply (parameterField ratio).mul_mem
    · split_ifs <;> simp
    · exact (parameterField ratio).pow_mem (ratio_mem_parameterField ratio) index

theorem periodic_address_mem_parameterField {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool) {period : ℕ} (period_positive : 0 < period)
    (periodic : ∀ index, digits (index+period) = digits index) :
    address ratio digits ∈ parameterField ratio := by
  have split := address_prefix_tail nonnegative less_one digits period
  have tails_equal : (fun index => digits (index+period)) = digits := funext periodic
  rw [tails_equal] at split
  have power_less : ratio ^ period < 1 := pow_lt_one₀ nonnegative less_one period_positive.ne'
  have denominator_nonzero : 1-ratio ^ period ≠ 0 := by linarith
  have coordinate_eq : address ratio digits = prefixValue ratio digits period / (1-ratio ^ period) := by
    apply (eq_div_iff denominator_nonzero).mpr
    nlinarith
  rw [coordinate_eq]
  exact (parameterField ratio).div_mem (prefixValue_mem_parameterField ratio digits period)
    ((parameterField ratio).sub_mem (parameterField ratio).one_mem
      ((parameterField ratio).pow_mem (ratio_mem_parameterField ratio) period))

/-- Every eventually periodic Cantor address lies in ℚ(λ), including the
eventually constant and eventually alternating addresses in Section 4. -/
theorem eventually_periodic_address_mem_parameterField {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool) (prefixLength period : ℕ) (period_positive : 0 < period)
    (periodic : ∀ index, digits (index+prefixLength+period) = digits (index+prefixLength)) :
    address ratio digits ∈ parameterField ratio := by
  rw [address_prefix_tail nonnegative less_one digits prefixLength]
  apply (parameterField ratio).add_mem (prefixValue_mem_parameterField ratio digits prefixLength)
  apply (parameterField ratio).mul_mem
    ((parameterField ratio).pow_mem (ratio_mem_parameterField ratio) prefixLength)
  apply periodic_address_mem_parameterField nonnegative less_one
    (fun index => digits (index+prefixLength)) period_positive
  intro index
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using periodic index

end LambdaCantor.Last
