import LambdaCantor.Last.GapCoverage
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace LambdaCantor.Last

/-- The open interval misses every integer translate of the actual scaled
address Cantor set. No classification of complementary arcs is assumed. -/
def ScaledCantorCircleAvoids (ratio scale left right : ℝ) : Prop :=
  ∀ coordinate ∈ cantorSet ratio, ∀ translate : ℤ,
    scale*coordinate+(translate : ℝ) ∉ Set.Ioo left right

/-- An actual empty interval in the scaled hull either has the nonroot gap
bound or is contained in the scaled root gap. Its endpoints need not be
Cantor points. The actual central-gap cover supplies the containing gap. -/
theorem scaled_cantor_empty_interval_root_or_small {ratio scale left right : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (scale_positive : 0 < scale) (scale_ratio : scale*ratio ≤ 1)
    (left_lower : 0 ≤ left) (right_upper : right ≤ scale) (ordered : left < right)
    (empty_interval : ∀ coordinate ∈ cantorSet ratio,
      scale*coordinate ∉ Set.Ioo left right) :
    right-left ≤ 1-2*ratio ∨
      (scale*ratio ≤ left ∧ right ≤ scale*(1-ratio)) := by
  have less_one : ratio < 1 := by linarith
  have midpoint_lower : left < (left+right)/2 := by linarith
  have midpoint_upper : (left+right)/2 < right := by linarith
  have normalized_bounds : (left+right)/2/scale ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith) scale_positive.le
    · apply (div_le_one scale_positive).mpr
      linarith
  have outside : (left+right)/2/scale ∉ cantorSet ratio := by
    intro membership
    apply empty_interval _ membership
    rw [mul_div_cancel₀ _ scale_positive.ne']
    exact ⟨midpoint_lower, midpoint_upper⟩
  have in_gap_cover : (left+right)/2/scale ∈
      ⋃ word : List Bool, scalarWordMap ratio word '' Set.Ioo ratio (1-ratio) := by
    rw [← central_gaps_cover_complement positive less_half]
    exact ⟨normalized_bounds, outside⟩
  obtain ⟨word, gap_coordinate, gap_membership, representation⟩ := Set.mem_iUnion.mp in_gap_cover
  have in_gap : (left+right)/2/scale ∈
      Set.Ioo (scalarWordMap ratio word ratio) (scalarWordMap ratio word (1-ratio)) := by
    rw [← scalarWordMap_image_Ioo positive]
    exact ⟨gap_coordinate, gap_membership, representation⟩
  have gap_left_before_midpoint : scale*scalarWordMap ratio word ratio < (left+right)/2 := by
    have bound := mul_lt_mul_of_pos_left in_gap.1 scale_positive
    simpa only [mul_div_cancel₀ _ scale_positive.ne'] using bound
  have midpoint_before_gap_right : (left+right)/2 < scale*scalarWordMap ratio word (1-ratio) := by
    have bound := mul_lt_mul_of_pos_left in_gap.2 scale_positive
    simpa only [mul_div_cancel₀ _ scale_positive.ne'] using bound
  have left_endpoint_mem : scalarWordMap ratio word ratio ∈ cantorSet ratio := by
    apply scalarWordMap_mem_cantorSet positive.le less_one
    simpa using low_copy_mem positive.le less_one (one_mem_cantorSet positive.le less_one)
  have right_endpoint_mem : scalarWordMap ratio word (1-ratio) ∈ cantorSet ratio := by
    apply scalarWordMap_mem_cantorSet positive.le less_one
    simpa using high_copy_mem positive.le less_one (zero_mem_cantorSet ratio)
  have left_bound : scale*scalarWordMap ratio word ratio ≤ left := by
    by_contra failure
    exact empty_interval _ left_endpoint_mem ⟨lt_of_not_ge failure,
      gap_left_before_midpoint.trans midpoint_upper⟩
  have right_bound : right ≤ scale*scalarWordMap ratio word (1-ratio) := by
    by_contra failure
    exact empty_interval _ right_endpoint_mem ⟨midpoint_lower.trans midpoint_before_gap_right,
      lt_of_not_ge failure⟩
  by_cases root : word = []
  · right
    simpa [root, scalarWordMap] using And.intro left_bound right_bound
  · left
    have depth_positive : 1 ≤ word.length := by
      cases word with
      | nil => exact False.elim (root rfl)
      | cons digit rest => simp
    have power_bound : ratio^word.length ≤ ratio := by
      simpa using pow_le_pow_of_le_one positive.le less_one.le depth_positive
    have scaled_power_bound : scale*ratio^word.length ≤ 1 :=
      (mul_le_mul_of_nonneg_left power_bound scale_positive.le).trans scale_ratio
    have gap_width : scale*scalarWordMap ratio word (1-ratio)-
        scale*scalarWordMap ratio word ratio = scale*ratio^word.length*(1-2*ratio) := by
      rw [scalarWordMap_affine ratio word (1-ratio), scalarWordMap_affine ratio word ratio]
      ring
    have width_bound : right-left ≤ scale*ratio^word.length*(1-2*ratio) := by
      rw [← gap_width]
      linarith
    exact width_bound.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right scaled_power_bound
        (show 0 ≤ 1-2*ratio by linarith))

/-- For a normalized actual empty circle arc longer than a nonroot gap,
both the root-gap width and the overlap of its two adjacent translates
bound its length. -/
theorem scaled_cantor_circle_normalized_root_bounds {ratio scale left right : ℝ}
    (above_third : (1/3 : ℝ) ≤ ratio) (less_half : ratio < 1/2)
    (scale_lower : 1 ≤ scale) (scale_upper : scale < 1/ratio)
    (left_lower : 0 ≤ left) (right_upper : right ≤ 1) (ordered : left < right)
    (empty_arc : ScaledCantorCircleAvoids ratio scale left right)
    (long_arc : 1-2*ratio < right-left) :
    right-left ≤ scale*(1-2*ratio) ∧ right-left ≤ 2-scale := by
  have positive : 0 < ratio := by linarith
  have less_one : ratio < 1 := by linarith
  have scale_positive : 0 < scale := by linarith
  have scale_ratio : scale*ratio < 1 := (lt_div_iff₀ positive).mp scale_upper
  have root_width : scale*(1-2*ratio) < 1 := by
    have comparison := mul_le_mul_of_nonneg_left (show 1-2*ratio ≤ ratio by linarith) scale_positive.le
    linarith
  have empty_original : ∀ coordinate ∈ cantorSet ratio,
      scale*coordinate ∉ Set.Ioo left right := by
    intro coordinate membership
    simpa using empty_arc coordinate membership 0
  have root := scaled_cantor_empty_interval_root_or_small positive less_half scale_positive
    scale_ratio.le left_lower (right_upper.trans scale_lower) ordered empty_original
  have root_bounds : scale*ratio ≤ left ∧ right ≤ scale*(1-ratio) := by
    rcases root with small | bounds
    · exact False.elim (not_le_of_gt long_arc small)
    · exact bounds
  have empty_translated : ∀ coordinate ∈ cantorSet ratio,
      scale*coordinate ∉ Set.Ioo (left+1) (right+1) := by
    intro coordinate membership inside
    apply empty_arc coordinate membership (-1)
    simp only [Int.cast_neg, Int.cast_one, Set.mem_Ioo]
    constructor <;> linarith [inside.1, inside.2]
  have endpoint_outside : scale ∉ Set.Ioo (left+1) (right+1) := by
    simpa using empty_translated 1 (one_mem_cantorSet positive.le less_one)
  have translated_after_hull : scale ≤ left+1 := by
    by_contra failure
    have translated_upper : right+1 ≤ scale := by
      by_contra upper_failure
      exact endpoint_outside ⟨lt_of_not_ge failure, lt_of_not_ge upper_failure⟩
    have translated_root := scaled_cantor_empty_interval_root_or_small positive less_half
      scale_positive scale_ratio.le (by linarith) translated_upper (by linarith) empty_translated
    rcases translated_root with small | bounds
    · exact not_le_of_gt long_arc (by linarith)
    · linarith [root_bounds.1, bounds.2]
  constructor
  · linarith [root_bounds.1, root_bounds.2]
  · linarith

theorem scaled_cantor_circle_normalized_gap_bound {ratio scale left right : ℝ}
    (above_third : (1/3 : ℝ) ≤ ratio) (less_half : ratio < 1/2)
    (scale_lower : 1 ≤ scale) (scale_upper : scale < 1/ratio)
    (left_lower : 0 ≤ left) (right_upper : right ≤ 1) (ordered : left < right)
    (empty_arc : ScaledCantorCircleAvoids ratio scale left right) :
    right-left ≤ max (1-2*ratio) (min (scale*(1-2*ratio)) (2-scale)) := by
  by_cases small : right-left ≤ 1-2*ratio
  · exact small.trans (le_max_left _ _)
  · have bounds := scaled_cantor_circle_normalized_root_bounds above_third less_half
      scale_lower scale_upper left_lower right_upper ordered empty_arc (lt_of_not_ge small)
    exact (le_min bounds.1 bounds.2).trans (le_max_right _ _)

/-- The three-piece circle estimate applies to every open interval and all
integer translates. Integer normalization is proved using the actual point
zero of the Cantor set, rather than imposed as an arc convention. -/
theorem scaled_cantor_circle_gap_bound {ratio scale left right : ℝ}
    (above_third : (1/3 : ℝ) ≤ ratio) (less_half : ratio < 1/2)
    (scale_lower : 1 ≤ scale) (scale_upper : scale < 1/ratio)
    (empty_arc : ScaledCantorCircleAvoids ratio scale left right) :
    right-left ≤ max (1-2*ratio) (min (scale*(1-2*ratio)) (2-scale)) := by
  by_cases ordered : left < right
  · have floor_lower := Int.floor_le left
    have floor_upper := Int.lt_floor_add_one left
    have right_bound : right ≤ (⌊left⌋ : ℤ)+1 := by
      by_contra failure
      apply empty_arc 0 (zero_mem_cantorSet ratio) (⌊left⌋+1)
      simp only [mul_zero, zero_add, Int.cast_add, Int.cast_one, Set.mem_Ioo]
      exact ⟨floor_upper, lt_of_not_ge failure⟩
    have normalized_empty : ScaledCantorCircleAvoids ratio scale
        (left-(⌊left⌋ : ℤ)) (right-(⌊left⌋ : ℤ)) := by
      intro coordinate membership translate inside
      apply empty_arc coordinate membership (translate+⌊left⌋)
      simp only [Int.cast_add, Set.mem_Ioo]
      constructor <;> linarith [inside.1, inside.2]
    have normalized_bound := scaled_cantor_circle_normalized_gap_bound above_third less_half
      scale_lower scale_upper (show 0 ≤ left-(⌊left⌋ : ℤ) by linarith)
      (show right-(⌊left⌋ : ℤ) ≤ 1 by linarith) (by linarith) normalized_empty
    linarith
  · have positive_bound : 0 < 1-2*ratio := by linarith
    exact (show right-left ≤ 1-2*ratio by linarith).trans (le_max_left _ _)

theorem scaled_cantor_circle_first_piece {ratio scale left right : ℝ}
    (above_third : (1/3 : ℝ) ≤ ratio) (less_half : ratio < 1/2)
    (scale_lower : 1 ≤ scale) (scale_upper : scale < 1/ratio)
    (empty_arc : ScaledCantorCircleAvoids ratio scale left right) :
    right-left ≤ scale*(1-2*ratio) := by
  apply (scaled_cantor_circle_gap_bound above_third less_half scale_lower scale_upper empty_arc).trans
  apply max_le
  · nlinarith [mul_nonneg (show 0 ≤ scale-1 by linarith) (show 0 ≤ 1-2*ratio by linarith)]
  · exact min_le_left _ _

theorem scaled_cantor_circle_middle_piece {ratio scale left right : ℝ}
    (above_third : (1/3 : ℝ) ≤ ratio) (less_half : ratio < 1/2)
    (scale_lower : 1 ≤ scale) (scale_upper : scale < 1/ratio)
    (middle_upper : scale ≤ 1+2*ratio)
    (empty_arc : ScaledCantorCircleAvoids ratio scale left right) :
    right-left ≤ 2-scale := by
  apply (scaled_cantor_circle_gap_bound above_third less_half scale_lower scale_upper empty_arc).trans
  exact max_le (by linarith) (min_le_right _ _)

theorem scaled_cantor_circle_last_piece {ratio scale left right : ℝ}
    (above_third : (1/3 : ℝ) ≤ ratio) (less_half : ratio < 1/2)
    (scale_lower : 1 ≤ scale) (scale_upper : scale < 1/ratio)
    (last_lower : 1+2*ratio ≤ scale)
    (empty_arc : ScaledCantorCircleAvoids ratio scale left right) :
    right-left ≤ 1-2*ratio := by
  apply (scaled_cantor_circle_gap_bound above_third less_half scale_lower scale_upper empty_arc).trans
  exact max_le le_rfl ((min_le_right _ _).trans (by linarith))

end LambdaCantor.Last
