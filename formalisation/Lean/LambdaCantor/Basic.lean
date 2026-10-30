import LambdaCantor.Common
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

noncomputable section
namespace LambdaCantor

theorem address_summable {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digits : ℕ → Bool) :
    Summable (fun j : ℕ => (if digits j then (1 : ℝ) else 0) * ratio ^ j) := by
  apply Summable.of_nonneg_of_le
    (fun j => by split_ifs <;> positivity)
    (fun j => by split_ifs <;> simp [pow_nonneg nonnegative])
    (summable_geometric_of_lt_one nonnegative less_one)

theorem address_nonnegative {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digits : ℕ → Bool) : 0 ≤ address ratio digits := by
  unfold address
  apply mul_nonneg (by linarith)
  exact tsum_nonneg (fun j => by split_ifs <;> positivity)

theorem address_le_one {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (digits : ℕ → Bool) : address ratio digits ≤ 1 := by
  unfold address
  have bound := (address_summable nonnegative less_one digits).tsum_le_tsum
    (fun j => show (if digits j then (1 : ℝ) else 0) * ratio ^ j ≤ ratio ^ j by
      split_ifs <;> simp [pow_nonneg nonnegative])
    (summable_geometric_of_lt_one nonnegative less_one)
  rw [tsum_geometric_of_lt_one nonnegative less_one] at bound
  calc
    (1 - ratio) * ∑' j : ℕ, (if digits j then (1 : ℝ) else 0) * ratio ^ j
      ≤ (1 - ratio) * (1 - ratio)⁻¹ := mul_le_mul_of_nonneg_left bound (by linarith)
    _ = 1 := mul_inv_cancel₀ (by linarith)

theorem cantorSet_subset_unitInterval {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : cantorSet ratio ⊆ Set.Icc 0 1 := by
  rintro x ⟨digits, rfl⟩
  exact ⟨address_nonnegative nonnegative less_one digits,
    address_le_one nonnegative less_one digits⟩

theorem one_mem_cantorSet {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : 1 ∈ cantorSet ratio := by
  refine ⟨fun _ => true, ?_⟩
  simp only [address, if_true, one_mul]
  rw [tsum_geometric_of_lt_one nonnegative less_one]
  exact mul_inv_cancel₀ (by linarith)

theorem continuous_address {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : Continuous (address ratio) := by
  unfold address
  apply Continuous.const_mul
  apply continuous_tsum (u := fun j : ℕ => ratio ^ j)
  · intro j
    have continuous_digit : Continuous (fun b : Bool => if b then (1 : ℝ) else 0) :=
      continuous_of_discreteTopology
    exact (continuous_digit.comp (continuous_apply j)).mul continuous_const
  · exact summable_geometric_of_lt_one nonnegative less_one
  · intro j digits
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg nonnegative, pow_nonneg nonnegative]

theorem isCompact_cantorSet {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : IsCompact (cantorSet ratio) := by
  exact isCompact_range (continuous_address nonnegative less_one)

theorem isCompact_intersection {exponent ratio : ℝ} (exponent_positive : 0 < exponent)
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1) :
    IsCompact (intersection exponent ratio) := by
  have continuous_equation : Continuous (fun point : ℝ × ℝ =>
      point.1 ^ exponent + point.2 ^ exponent) := by
    have : 0 ≤ exponent := le_of_lt exponent_positive
    fun_prop
  have compact := ((isCompact_cantorSet nonnegative less_one).prod
    (isCompact_cantorSet nonnegative less_one)).inter_right
      (isClosed_eq continuous_equation (continuous_const (y := (1 : ℝ))))
  convert compact using 1
  ext point
  simp only [intersection, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
  tauto

end LambdaCantor
