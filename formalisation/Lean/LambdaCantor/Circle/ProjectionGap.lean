import LambdaCantor.Circle.Onset
import LambdaCantor.Certificates.CirclePolynomials

noncomputable section
namespace LambdaCantor.Circle

/-- The first gap of `(1-ratio) C + C`, as a statement about the genuine
address-defined Cantor sets, rather than an assumed projection enclosure. -/
theorem projection_first_gap {ratio firstTail secondTail : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (first_mem : firstTail ∈ cantorSet ratio)
    (second_mem : secondTail ∈ cantorSet ratio) :
    (1 - ratio) * firstTail + secondTail ≤ ratio * (2 - ratio) ∨
      (1 - ratio) ^ 2 ≤ (1 - ratio) * firstTail + secondTail := by
  have first_bounds := cantorSet_subset_unitInterval nonnegative less_one first_mem
  have second_bounds := cantorSet_subset_unitInterval nonnegative less_one second_mem
  rcases cantor_first_level_bounds nonnegative less_one first_mem with first_left | first_right
  · rcases cantor_first_level_bounds nonnegative less_one second_mem with second_left | second_right
    · left
      have : (1 - ratio) * firstTail ≤ (1 - ratio) * ratio :=
        mul_le_mul_of_nonneg_left first_left (by linarith)
      nlinarith
    · right
      have : 0 ≤ (1 - ratio) * firstTail := mul_nonneg (by linarith) first_bounds.1
      nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr less_one.le)]
  · right
    have : (1 - ratio) * (1 - ratio) ≤ (1 - ratio) * firstTail :=
      mul_le_mul_of_nonneg_left first_right (by linarith)
    nlinarith [second_bounds.1]

theorem projection_not_in_first_gap {ratio firstTail secondTail : ℝ}
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (first_mem : firstTail ∈ cantorSet ratio)
    (second_mem : secondTail ∈ cantorSet ratio) :
    ¬ (ratio * (2 - ratio) < (1 - ratio) * firstTail + secondTail ∧
      (1 - ratio) * firstTail + secondTail < (1 - ratio) ^ 2) := by
  have gap := projection_first_gap (by linarith : 0 ≤ ratio) (by linarith : ratio < 1)
    first_mem second_mem
  rcases gap with gap | gap <;> intro membership <;> linarith [membership.1, membership.2]

/-- The later-scale candidate interval in the paper lies entirely in this
first gap. The algebraic error estimate is supplied explicitly. -/
theorem later_scale_projection_exclusion {ratio firstTail secondTail level scaleError : ℝ}
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (first_mem : firstTail ∈ cantorSet ratio)
    (second_mem : secondTail ∈ cantorSet ratio)
    (level_lower : (379 / 100 : ℝ) < level)
    (level_upper : level < (381 / 100 : ℝ))
    (error_nonnegative : 0 ≤ scaleError) (error_upper : scaleError ≤ ratio ^ 2)
    (candidate_lower : ratio / 2 * (level - scaleError) - ratio ^ 7 / 2 ≤
      (1 - ratio) * firstTail + secondTail)
    (candidate_upper : (1 - ratio) * firstTail + secondTail ≤
      ratio / 2 * (level - scaleError) + ratio ^ 7) : False := by
  have lower_gap := later_lower_certificate ratio lower upper
  have upper_gap := later_upper_certificate ratio lower upper
  have ratio_positive : 0 < ratio := by linarith
  have lower_comparison : ratio / 2 * (379 / 100 - ratio ^ 2) - ratio ^ 7 / 2 ≤
      ratio / 2 * (level - scaleError) - ratio ^ 7 / 2 := by nlinarith
  have upper_comparison : ratio / 2 * (level - scaleError) + ratio ^ 7 ≤
      381 * ratio / 200 + ratio ^ 7 := by nlinarith
  apply projection_not_in_first_gap lower upper first_mem second_mem
  constructor <;> linarith

theorem projection_bounds {ratio firstTail secondTail : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio) :
    0 ≤ (1 - ratio) * firstTail + secondTail ∧
      (1 - ratio) * firstTail + secondTail ≤ 2 - ratio := by
  have first_bounds := cantorSet_subset_unitInterval nonnegative less_one first_mem
  have second_bounds := cantorSet_subset_unitInterval nonnegative less_one second_mem
  have lower_product := mul_nonneg (sub_nonneg.mpr less_one.le) first_bounds.1
  have upper_product := mul_le_mul_of_nonneg_left first_bounds.2 (sub_nonneg.mpr less_one.le)
  constructor <;> nlinarith [second_bounds.1, second_bounds.2]

theorem projection_step {ratio firstTail secondTail : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio) :
    ∃ nextFirst ∈ cantorSet ratio, ∃ nextSecond ∈ cantorSet ratio,
      (1 - ratio) * firstTail + secondTail = ratio * ((1 - ratio) * nextFirst + nextSecond) ∨
      (1 - ratio) * firstTail + secondTail = (1 - ratio) ^ 2 + ratio * ((1 - ratio) * nextFirst + nextSecond) ∨
      (1 - ratio) * firstTail + secondTail = (1 - ratio) + ratio * ((1 - ratio) * nextFirst + nextSecond) ∨
      (1 - ratio) * firstTail + secondTail = (1 - ratio) * (2 - ratio) + ratio * ((1 - ratio) * nextFirst + nextSecond) := by
  rcases first_mem with ⟨firstDigits, rfl⟩
  rcases second_mem with ⟨secondDigits, rfl⟩
  refine ⟨address ratio (fun j => firstDigits (j + 1)), ⟨_, rfl⟩,
    address ratio (fun j => secondDigits (j + 1)), ⟨_, rfl⟩, ?_⟩
  rw [address_first_digit nonnegative less_one firstDigits,
    address_first_digit nonnegative less_one secondDigits]
  cases first : firstDigits 0 <;> cases second : secondDigits 0 <;>
    simp only [first, second, Bool.false_eq_true, if_false, if_true, mul_zero, mul_one, zero_add]
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inr (Or.inl (by ring)))
  · exact Or.inr (Or.inl (by ring))
  · exact Or.inr (Or.inr (Or.inr (by ring)))

theorem projection_leftmost_child {ratio firstTail secondTail : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio)
    (below : (1 - ratio) * firstTail + secondTail < (1 - ratio) ^ 2) :
    ∃ nextFirst ∈ cantorSet ratio, ∃ nextSecond ∈ cantorSet ratio,
      (1 - ratio) * firstTail + secondTail = ratio * ((1 - ratio) * nextFirst + nextSecond) := by
  obtain ⟨nextFirst, first_mem, nextSecond, second_mem, alternatives⟩ :=
    projection_step nonnegative less_one first_mem second_mem
  have bounds := projection_bounds nonnegative less_one first_mem second_mem
  have product_nonnegative := mul_nonneg nonnegative bounds.1
  have ratio_product := mul_nonneg nonnegative (sub_nonneg.mpr less_one.le)
  refine ⟨nextFirst, first_mem, nextSecond, second_mem, ?_⟩
  rcases alternatives with equality | equality | equality | equality
  · exact equality
  · nlinarith
  · nlinarith
  · nlinarith [sq_nonneg ratio]

theorem projection_rightmost_child {ratio firstTail secondTail : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio)
    (above : (1 - ratio) + ratio * (2 - ratio) < (1 - ratio) * firstTail + secondTail) :
    ∃ nextFirst ∈ cantorSet ratio, ∃ nextSecond ∈ cantorSet ratio,
      (1 - ratio) * firstTail + secondTail =
        (1 - ratio) * (2 - ratio) + ratio * ((1 - ratio) * nextFirst + nextSecond) := by
  obtain ⟨nextFirst, first_mem, nextSecond, second_mem, alternatives⟩ :=
    projection_step nonnegative less_one first_mem second_mem
  have bounds := projection_bounds nonnegative less_one first_mem second_mem
  have product_bounded := mul_le_mul_of_nonneg_left bounds.2 nonnegative
  have ratio_product := mul_nonneg nonnegative (sub_nonneg.mpr less_one.le)
  refine ⟨nextFirst, first_mem, nextSecond, second_mem, ?_⟩
  rcases alternatives with equality | equality | equality | equality
  · nlinarith
  · nlinarith
  · nlinarith
  · exact equality

/-- The smaller displayed gap is a gap of the whole projection: its first
paired digits are forced to `00` and then `11`, after which the first gap
applies to the remaining genuine Cantor tails. -/
theorem projection_not_in_nested_gap {ratio firstTail secondTail : ℝ}
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio) :
    ¬ (ratio * (1 - ratio) * (2 - ratio) + ratio ^ 3 * (2 - ratio) <
          (1 - ratio) * firstTail + secondTail ∧
      (1 - ratio) * firstTail + secondTail <
        ratio * (1 - ratio) * (2 - ratio) + ratio ^ 2 * (1 - ratio) ^ 2) := by
  intro membership
  have positive : 0 < ratio := by linarith
  have less_one : ratio < 1 := by linarith
  have below := nested_below_certificate ratio lower upper
  have above := nested_above_certificate ratio lower upper
  obtain ⟨nextFirst, nextFirst_mem, nextSecond, nextSecond_mem, first_step⟩ :=
    projection_leftmost_child positive.le less_one first_mem second_mem (by nlinarith [membership.2])
  have next_above : (1 - ratio) + ratio * (2 - ratio) < (1 - ratio) * nextFirst + nextSecond := by
    have difference_positive : 0 < ratio * ((1 - ratio) ^ 2 - ratio * (1 - ratio) * (2 - ratio)) :=
      mul_pos positive (by linarith)
    have multiplied : ratio * ((1 - ratio) + ratio * (2 - ratio)) <
        ratio * ((1 - ratio) * nextFirst + nextSecond) := by nlinarith [membership.1]
    exact (mul_lt_mul_iff_of_pos_left positive).mp multiplied
  obtain ⟨lastFirst, lastFirst_mem, lastSecond, lastSecond_mem, second_step⟩ :=
    projection_rightmost_child positive.le less_one nextFirst_mem nextSecond_mem next_above
  apply projection_not_in_first_gap lower upper lastFirst_mem lastSecond_mem
  have combined : (1 - ratio) * firstTail + secondTail =
      ratio * ((1 - ratio) * (2 - ratio) + ratio * ((1 - ratio) * lastFirst + lastSecond)) := by
    rw [first_step, second_step]
  have square_positive : 0 < ratio ^ 2 := sq_pos_of_pos positive
  constructor
  · apply (mul_lt_mul_iff_of_pos_left square_positive).mp
    nlinarith [membership.1]
  · apply (mul_lt_mul_iff_of_pos_left square_positive).mp
    nlinarith [membership.2]

theorem first_scale_projection_exclusion {ratio firstTail secondTail level : ℝ}
    (lower : (2679 / 10000 : ℝ) ≤ ratio) (upper : ratio ≤ (67 / 250 : ℝ))
    (first_mem : firstTail ∈ cantorSet ratio) (second_mem : secondTail ∈ cantorSet ratio)
    (level_lower : (379 / 100 : ℝ) < level) (level_upper : level < (381 / 100 : ℝ))
    (candidate_lower : ratio / 2 * (level - 1) - ratio ^ 7 / 2 ≤ (1 - ratio) * firstTail + secondTail)
    (candidate_upper : (1 - ratio) * firstTail + secondTail ≤ ratio / 2 * (level - 1) + ratio ^ 7) : False := by
  have lower_gap := first_lower_certificate ratio lower upper
  have upper_gap := first_upper_certificate ratio lower upper
  have ratio_positive : 0 < ratio := by linarith
  have lower_comparison : 279 * ratio / 200 - ratio ^ 7 / 2 ≤ ratio / 2 * (level - 1) - ratio ^ 7 / 2 := by nlinarith
  have upper_comparison : ratio / 2 * (level - 1) + ratio ^ 7 ≤ 281 * ratio / 200 + ratio ^ 7 := by nlinarith
  apply projection_not_in_nested_gap lower upper first_mem second_mem
  constructor <;> linarith

end LambdaCantor.Circle
