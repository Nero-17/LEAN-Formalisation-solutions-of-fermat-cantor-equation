import LambdaCantor.Integer.FixedSignedLog
import Mathlib.Algebra.Order.Floor.Ring

namespace LambdaCantor.Integer

/-- A cover of all fractional phases yields a nonnegative integer depth.
The lower-bound hypothesis prevents silently replacing a signed shift by a
natural exponent. -/
theorem phase_cover_natural_shift {ι : Type*} (valid : ι → Prop)
    (lower upper : ι → ℝ) (rotation : ℝ)
    (covered : ∀ phase ∈ Set.Icc (0 : ℝ) 1, ∃ source : ι, ∃ shift : ℤ,
      valid source ∧ lower source < phase+shift ∧ phase+shift < upper source)
    (rotationBelow : ∀ source, valid source → rotation ≤ lower source) :
    ∃ source : ι, ∃ depth : ℕ,
      valid source ∧ lower source < rotation+depth ∧ rotation+depth < upper source := by
  obtain ⟨source,shift,sourceValid,sourceLower,sourceUpper⟩ := covered (Int.fract rotation)
    ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩
  have floorIdentity := Int.floor_add_fract rotation
  have depthPositive : (0 : ℝ) < ((shift-⌊rotation⌋ : ℤ) : ℝ) := by
    push_cast
    linarith [rotationBelow source sourceValid]
  have depthNonnegative : (0 : ℤ) ≤ shift-⌊rotation⌋ := by
    have positive : (0 : ℤ) < shift-⌊rotation⌋ := by exact_mod_cast depthPositive
    omega
  have depthCast : (((shift-⌊rotation⌋).toNat : ℕ) : ℝ) = (shift : ℝ)-(⌊rotation⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg depthNonnegative
  refine ⟨source,(shift-⌊rotation⌋).toNat,sourceValid,?_,?_⟩ <;> rw [depthCast] <;> linarith

theorem centered_log_phase_lower_ge_rotation (n center horizontalRight verticalLeft : ℝ)
    (positiveN : 0 < n) (centerPositive : 0 < center)
    (horizontalPositive : 0 < horizontalRight) (horizontalBound : horizontalRight ≤ 1)
    (verticalPositive : 0 < verticalLeft) (productBound : 1 ≤ n*verticalLeft) :
    (n*Real.log center-Real.log n)/Real.log 3 ≤
      (Real.log verticalLeft+n*Real.log (center/horizontalRight))/Real.log 3 := by
  apply (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 3))).2
  rw [Real.log_div (ne_of_gt centerPositive) (ne_of_gt horizontalPositive)]
  have horizontalLog := mul_nonpos_of_nonneg_of_nonpos positiveN.le
    (Real.log_nonpos horizontalPositive.le horizontalBound)
  have productLog := Real.log_nonneg productBound
  rw [Real.log_mul (ne_of_gt positiveN) (ne_of_gt verticalPositive)] at productLog
  linarith

/-- Removing the common rotation converts the checked phase interval into
the exact two strict logarithmic corner inequalities used by near-axis transfer. -/
theorem centered_log_phase_corners (n : ℕ) (depth : ℕ)
    (center horizontalLeft horizontalRight verticalLeft verticalRight : ℝ)
    (positiveN : 0 < n) (centerPositive : 0 < center)
    (leftPositive : 0 < horizontalLeft) (rightPositive : 0 < horizontalRight)
    (lower : (Real.log verticalLeft+(n : ℝ)*Real.log (center/horizontalRight))/Real.log 3 <
      ((n : ℝ)*Real.log center-Real.log n)/Real.log 3+depth)
    (upper : ((n : ℝ)*Real.log center-Real.log n)/Real.log 3+depth <
      (Real.log verticalRight+(n : ℝ)*Real.log (center/horizontalLeft))/Real.log 3) :
    (n : ℝ)*Real.log horizontalLeft-Real.log verticalRight-Real.log n+
        (depth : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log horizontalRight-Real.log verticalLeft-Real.log n+
        (depth : ℝ)*Real.log 3 := by
  have logPositive : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have lowerCleared := (div_lt_iff₀ logPositive).1 lower
  have upperCleared := (lt_div_iff₀ logPositive).1 upper
  rw [Real.log_div (ne_of_gt centerPositive) (ne_of_gt rightPositive)] at lowerCleared
  rw [Real.log_div (ne_of_gt centerPositive) (ne_of_gt leftPositive)] at upperCleared
  have cancel : (((n : ℝ)*Real.log center-Real.log n)/Real.log 3)*Real.log 3 =
      (n : ℝ)*Real.log center-Real.log n := div_mul_cancel₀ _ (ne_of_gt logPositive)
  constructor <;> nlinarith

end LambdaCantor.Integer
