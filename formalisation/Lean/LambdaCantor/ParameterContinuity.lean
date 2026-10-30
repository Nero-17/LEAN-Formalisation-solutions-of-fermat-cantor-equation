import LambdaCantor.Basic
import Mathlib.Tactic.GCongr

noncomputable section
namespace LambdaCantor

theorem continuous_address_band {lower upper : ℝ} (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper) :
    Continuous (fun point : Set.Icc lower upper × (ℕ → Bool) =>
      address point.1.val point.2) := by
  have upper_nonnegative : 0 ≤ upper := lower_nonnegative.trans ordered
  unfold address
  apply Continuous.mul
  · fun_prop
  apply continuous_tsum (u := fun j : ℕ => upper ^ j)
  · intro j
    have digit_continuous : Continuous (fun bit : Bool => if bit then (1 : ℝ) else 0) :=
      continuous_of_discreteTopology
    exact (digit_continuous.comp ((continuous_apply j).comp continuous_snd)).mul
      ((continuous_subtype_val.comp continuous_fst).pow j)
  · exact summable_geometric_of_lt_one upper_nonnegative upper_lt_one
  · intro j point
    have ratio_nonnegative := lower_nonnegative.trans point.1.property.1
    split_ifs
    · simp only [one_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg ratio_nonnegative]
      exact pow_le_pow_left₀ ratio_nonnegative point.1.property.2 j
    · simp [pow_nonneg upper_nonnegative]

theorem isCompact_parameter_dust {lower upper : ℝ} (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper) :
    IsCompact {point : ℝ × (ℝ × ℝ) | point.1 ∈ Set.Icc lower upper ∧
      point.2.1 ∈ cantorSet point.1 ∧ point.2.2 ∈ cantorSet point.1} := by
  let encode : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) → ℝ × (ℝ × ℝ) :=
    fun point => (point.1.val, (address point.1.val point.2.1, address point.1.val point.2.2))
  have encode_continuous : Continuous encode := by
    have address_continuous := continuous_address_band lower_nonnegative upper_lt_one ordered
    apply Continuous.prodMk (continuous_subtype_val.comp continuous_fst)
    apply Continuous.prodMk
    · exact address_continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    · exact address_continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have range_eq : Set.range encode = {point : ℝ × (ℝ × ℝ) | point.1 ∈ Set.Icc lower upper ∧
      point.2.1 ∈ cantorSet point.1 ∧ point.2.2 ∈ cantorSet point.1} := by
    ext point
    constructor
    · rintro ⟨⟨ratio, left, right⟩, rfl⟩
      exact ⟨ratio.property, ⟨left, rfl⟩, ⟨right, rfl⟩⟩
    · rintro ⟨ratio_mem, ⟨left, left_eq⟩, ⟨right, right_eq⟩⟩
      refine ⟨(⟨point.1, ratio_mem⟩, (left, right)), ?_⟩
      simp only [encode, left_eq, right_eq, Prod.eta]
  rw [← range_eq]
  exact isCompact_range encode_continuous

theorem isCompact_parameter_intersection {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper) :
    IsCompact {point : ℝ × (ℝ × ℝ) | point.1 ∈ Set.Icc lower upper ∧
      point.2 ∈ intersection exponent point.1} := by
  have exponent_nonnegative := exponent_positive.le
  have equation_continuous : Continuous (fun point : ℝ × (ℝ × ℝ) =>
      point.2.1 ^ exponent + point.2.2 ^ exponent) := by fun_prop
  have compact := (isCompact_parameter_dust lower_nonnegative upper_lt_one ordered).inter_right
    (isClosed_eq equation_continuous (continuous_const (y := (1 : ℝ))))
  convert compact using 1
  ext point
  simp only [intersection, Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

end LambdaCantor
