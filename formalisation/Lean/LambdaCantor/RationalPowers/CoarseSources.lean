import LambdaCantor.RationalPowers.LogSourcePhase
import LambdaCantor.Integer.PrefixConcatenation

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

structure CoarseSourceRow where
  horizontal : ℕ
  vertical : ℕ
deriving DecidableEq

/-- A cheap rational-only width test. A separate finite band predicate checks
the full derivative interval. No logarithm is recomputed for any exponent
accepted by this width branch of the low-denominator partition. -/
def CoarseSourceRow.WidthAccepted (row : CoarseSourceRow) (numerator denominator shift : ℕ) : Prop :=
  0 < numerator ∧ 0 < denominator ∧ 0 < row.horizontal ∧ 0 < row.vertical ∧
  ternaryPrefix row.horizontal 7 = true ∧ ternaryPrefix row.vertical 7 = true ∧
  (11 : ℚ)/(10*(denominator : ℚ)) <
    (((numerator : ℚ)/denominator)/(3 : ℚ)^shift)/(row.horizontal+1)+1/(row.vertical+1)

instance (row : CoarseSourceRow) (numerator denominator shift : ℕ) :
    Decidable (row.WidthAccepted numerator denominator shift) := by
  unfold CoarseSourceRow.WidthAccepted
  infer_instance

theorem scaled_log_width_lower (exponent scale horizontal vertical : ℝ)
    (exponent_positive : 0 < exponent) (scale_lower : 1 ≤ scale)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical) :
    (exponent/scale)/(horizontal+1)+1/(vertical+1) <
      exponent*Real.log (1+1/(scale*horizontal))+Real.log (1+1/vertical) := by
  have scale_positive : 0 < scale := by linarith
  have horizontal_log := log_one_add_inverse_gt (scale*horizontal) (mul_pos scale_positive horizontal_positive)
  have vertical_log := log_one_add_inverse_gt vertical vertical_positive
  have normalized_positive : 0 < exponent/scale := div_pos exponent_positive scale_positive
  have first_lower : (exponent/scale)/(horizontal+1) ≤ exponent/(scale*horizontal+1) := by
    apply (div_le_div_iff₀ (by positivity : 0 < horizontal+1) (by positivity : 0 < scale*horizontal+1)).mpr
    calc
      (exponent/scale)*(scale*horizontal+1) ≤ (exponent/scale)*(scale*(horizontal+1)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) normalized_positive.le
      _ = exponent*(horizontal+1) := by rw [← mul_assoc, div_mul_cancel₀ _ scale_positive.ne']
  have horizontal_width := mul_lt_mul_of_pos_left horizontal_log exponent_positive
  rw [mul_one_div] at horizontal_width
  have horizontal_strict : (exponent/scale)/(horizontal+1) <
      exponent*Real.log (1+1/(scale*horizontal)) := by
    exact first_lower.trans_lt horizontal_width
  linarith

/-- Every accepted coarse-width row gives an actual rational lattice phase
and two strict source corners. The horizontal ternary word is extended by
exact zero digits; there is no integer-exponent assumption. -/
theorem CoarseSourceRow.WidthAccepted.log_source {row : CoarseSourceRow}
    {numerator denominator shift : ℕ} (checked : row.WidthAccepted numerator denominator shift) :
    ∃ phase : ℤ,
      ternaryPrefix (row.horizontal*3^shift) (7+shift) = true ∧
      ternaryPrefix row.vertical 7 = true ∧
      ((phase : ℝ)/denominator)*Real.log 3+
        ((numerator : ℝ)/denominator)*Real.log (((row.horizontal*3^shift : ℕ) : ℝ)/3^(7+shift))-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((row.vertical+1 : ℝ)/3^7) < 0 ∧
      0 < ((phase : ℝ)/denominator)*Real.log 3+
        ((numerator : ℝ)/denominator)*Real.log ((((row.horizontal*3^shift : ℕ) : ℝ)+1)/3^(7+shift))-
        Real.log ((numerator : ℝ)/denominator)-Real.log ((row.vertical : ℝ)/3^7) := by
  obtain ⟨numerator_positive, denominator_positive, horizontal_positive, vertical_positive,
    horizontal_prefix, vertical_prefix, width⟩ := checked
  have numerator_real_positive : (0 : ℝ) < numerator := by exact_mod_cast numerator_positive
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  have horizontal_real_positive : (0 : ℝ) < row.horizontal := by exact_mod_cast horizontal_positive
  have vertical_real_positive : (0 : ℝ) < row.vertical := by exact_mod_cast vertical_positive
  have scale_lower : (1 : ℝ) ≤ (3 : ℝ)^shift := one_le_pow₀ (by norm_num)
  have scale_positive : 0 < (3 : ℝ)^shift := by positivity
  have casted : ((11/(10*(denominator : ℚ)) : ℚ) : ℝ) <
      (((((numerator : ℚ)/denominator)/(3 : ℚ)^shift)/(row.horizontal+1)+1/(row.vertical+1) : ℚ) : ℝ) :=
    (Rat.cast_lt (K := ℝ)).mpr width
  push_cast at casted
  have logarithmic_width := scaled_log_width_lower ((numerator : ℝ)/denominator) ((3 : ℝ)^shift)
    row.horizontal row.vertical (div_pos numerator_real_positive denominator_real_positive)
    scale_lower horizontal_real_positive vertical_real_positive
  have spacing := positive_width_exceeds_spacing denominator denominator_positive _
    (casted.trans logarithmic_width)
  obtain ⟨phase, first_corner, second_corner⟩ := strict_log_phase_of_width
    ((numerator : ℝ)/denominator) ((3 : ℝ)^shift*row.horizontal) (row.vertical : ℝ)
    (7+shift) 7 denominator (mul_pos scale_positive horizontal_real_positive) vertical_real_positive
    denominator_positive spacing
  have extended_prefix := ternaryPrefix_append row.horizontal 0 7 shift horizontal_prefix (ternaryPrefix_zero shift)
  refine ⟨phase, by simpa only [Nat.add_zero] using extended_prefix, vertical_prefix, ?_, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using first_corner
  · simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using second_corner

end LambdaCantor.RationalPowers

