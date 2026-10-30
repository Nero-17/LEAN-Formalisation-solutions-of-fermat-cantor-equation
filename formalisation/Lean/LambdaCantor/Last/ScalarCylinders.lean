import LambdaCantor.Last.CantorGapBound
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last

def scalarWordMap (ratio : ℝ) : List Bool → ℝ → ℝ
  | [], coordinate => coordinate
  | digit :: rest, coordinate =>
    (if digit then 1-ratio else 0) + ratio*scalarWordMap ratio rest coordinate

theorem scalarWordMap_append (ratio : ℝ) (first second : List Bool) (coordinate : ℝ) :
    scalarWordMap ratio (first++second) coordinate =
      scalarWordMap ratio first (scalarWordMap ratio second coordinate) := by
  induction first with
  | nil => rfl
  | cons digit rest induction => simp only [List.cons_append, scalarWordMap, induction]

theorem scalarWordMap_affine (ratio : ℝ) (word : List Bool) (coordinate : ℝ) :
    scalarWordMap ratio word coordinate = scalarWordMap ratio word 0 + ratio^word.length*coordinate := by
  induction word with
  | nil => simp [scalarWordMap]
  | cons digit rest induction =>
    simp only [scalarWordMap, List.length_cons, induction, pow_succ]
    ring

theorem scalarWordMap_image_Ioo {ratio : ℝ} (positive : 0 < ratio)
    (word : List Bool) (left right : ℝ) :
    scalarWordMap ratio word '' Set.Ioo left right =
      Set.Ioo (scalarWordMap ratio word left) (scalarWordMap ratio word right) := by
  have map_eq : scalarWordMap ratio word =
      fun coordinate => ratio^word.length*coordinate+scalarWordMap ratio word 0 := by
    funext coordinate
    rw [scalarWordMap_affine]
    ring
  calc
    scalarWordMap ratio word '' Set.Ioo left right =
        (fun coordinate => ratio^word.length*coordinate+scalarWordMap ratio word 0) '' Set.Ioo left right := by
      exact congrArg (fun function => function '' Set.Ioo left right) map_eq
    _ = Set.Ioo (ratio^word.length*left+scalarWordMap ratio word 0)
        (ratio^word.length*right+scalarWordMap ratio word 0) :=
      Set.image_affine_Ioo (pow_pos positive _) _ _ _
    _ = Set.Ioo (scalarWordMap ratio word left) (scalarWordMap ratio word right) := by
      congr 1
      · exact (congrFun map_eq left).symm
      · exact (congrFun map_eq right).symm

theorem scalarWordMap_image_Icc {ratio : ℝ} (positive : 0 < ratio)
    (word : List Bool) (left right : ℝ) :
    scalarWordMap ratio word '' Set.Icc left right =
      Set.Icc (scalarWordMap ratio word left) (scalarWordMap ratio word right) := by
  have map_eq : scalarWordMap ratio word =
      fun coordinate => ratio^word.length*coordinate+scalarWordMap ratio word 0 := by
    funext coordinate
    rw [scalarWordMap_affine]
    ring
  calc
    scalarWordMap ratio word '' Set.Icc left right =
        (fun coordinate => ratio^word.length*coordinate+scalarWordMap ratio word 0) '' Set.Icc left right := by
      exact congrArg (fun function => function '' Set.Icc left right) map_eq
    _ = Set.Icc (ratio^word.length*left+scalarWordMap ratio word 0)
        (ratio^word.length*right+scalarWordMap ratio word 0) :=
      Set.image_affine_Icc' (pow_pos positive _) _ _ _
    _ = Set.Icc (scalarWordMap ratio word left) (scalarWordMap ratio word right) := by
      congr 1
      · exact (congrFun map_eq left).symm
      · exact (congrFun map_eq right).symm

theorem scalarWordMap_bounds {ratio coordinate : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (word : List Bool) (bounds : coordinate ∈ Set.Icc (0 : ℝ) 1) :
    scalarWordMap ratio word coordinate ∈ Set.Icc (0 : ℝ) 1 := by
  induction word with
  | nil => exact bounds
  | cons digit rest induction =>
    have scaled_nonnegative := mul_nonneg nonnegative induction.1
    have scaled_upper := mul_le_mul_of_nonneg_left induction.2 nonnegative
    cases digit <;> simp only [scalarWordMap, Bool.false_eq_true, if_false, if_true, zero_add] <;>
      constructor <;> linarith

theorem scalarWordMap_mem_cantorSet {ratio coordinate : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (word : List Bool) (membership : coordinate ∈ cantorSet ratio) :
    scalarWordMap ratio word coordinate ∈ cantorSet ratio := by
  induction word with
  | nil => exact membership
  | cons digit rest induction =>
    cases digit
    · simpa [scalarWordMap] using low_copy_mem nonnegative less_one induction
    · simpa [scalarWordMap] using high_copy_mem nonnegative less_one induction

theorem exists_scalar_cylinder {ratio coordinate : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (depth : ℕ) (membership : coordinate ∈ cantorSet ratio) :
    ∃ word : List Bool, word.length = depth ∧
      ∃ tail ∈ cantorSet ratio, coordinate = scalarWordMap ratio word tail := by
  induction depth generalizing coordinate with
  | zero => exact ⟨[], rfl, coordinate, membership, rfl⟩
  | succ depth induction =>
    rw [cantorSet_selfsimilar nonnegative less_one] at membership
    rcases membership with ⟨tail, tail_mem, rfl⟩ | ⟨tail, tail_mem, rfl⟩
    · obtain ⟨word, length_eq, final_tail, final_mem, equation⟩ := induction tail_mem
      exact ⟨false::word, by simp [length_eq], final_tail, final_mem,
        by simp [scalarWordMap, ← equation]⟩
    · obtain ⟨word, length_eq, final_tail, final_mem, equation⟩ := induction tail_mem
      exact ⟨true::word, by simp [length_eq], final_tail, final_mem,
        by simp [scalarWordMap, ← equation]⟩

/-- Every cylinder survives deletion of all distinct gaps at no greater depth. -/
theorem scalar_gap_avoids_cylinder {ratio : ℝ} (positive : 0 < ratio)
    (less_half : ratio < 1/2) (gap_word cylinder_word : List Bool)
    (depth_order : gap_word.length ≤ cylinder_word.length) (different : gap_word ≠ cylinder_word)
    {gap_coordinate cylinder_coordinate : ℝ}
    (in_gap : gap_coordinate ∈ Set.Ioo ratio (1-ratio))
    (in_unit : cylinder_coordinate ∈ Set.Icc (0 : ℝ) 1) :
    scalarWordMap ratio gap_word gap_coordinate ≠
      scalarWordMap ratio cylinder_word cylinder_coordinate := by
  have less_one : ratio < 1 := by linarith
  have gap_in_unit : gap_coordinate ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [in_gap.1, in_gap.2]
  induction gap_word generalizing cylinder_word with
  | nil =>
    cases cylinder_word with
    | nil => exact False.elim (different rfl)
    | cons digit rest =>
      have bounds := scalarWordMap_bounds positive.le less_one rest in_unit
      have scaled_lower := mul_nonneg positive.le bounds.1
      have scaled_upper := mul_le_mul_of_nonneg_left bounds.2 positive.le
      cases digit <;> simp only [scalarWordMap, Bool.false_eq_true, if_false, if_true, zero_add] <;>
        intro equality <;> linarith [in_gap.1, in_gap.2]
  | cons digit rest induction =>
    cases cylinder_word with
    | nil => simp only [List.length_cons, List.length_nil] at depth_order; omega
    | cons other tail =>
      by_cases same_digit : digit = other
      · subst other
        have tail_different : rest ≠ tail := by
          intro equality
          exact different (by rw [equality])
        have tail_depth : rest.length ≤ tail.length := by
          simp only [List.length_cons] at depth_order
          omega
        intro equality
        apply induction tail tail_depth tail_different
        simp only [scalarWordMap] at equality
        exact mul_left_cancel₀ positive.ne' (add_left_cancel equality)
      · have first_bounds := scalarWordMap_bounds positive.le less_one rest gap_in_unit
        have second_bounds := scalarWordMap_bounds positive.le less_one tail in_unit
        have first_lower := mul_nonneg positive.le first_bounds.1
        have second_lower := mul_nonneg positive.le second_bounds.1
        have first_upper := mul_le_mul_of_nonneg_left first_bounds.2 positive.le
        have second_upper := mul_le_mul_of_nonneg_left second_bounds.2 positive.le
        cases digit <;> cases other <;>
          simp only [scalarWordMap, Bool.false_eq_true, if_false, if_true, zero_add] at * <;>
          first | exact False.elim (same_digit True.intro) | intro equality; linarith

theorem scalar_central_gap_disjoint {ratio : ℝ} (positive : 0 < ratio)
    (less_half : ratio < 1/2) (word : List Bool) :
    Disjoint (scalarWordMap ratio word '' Set.Ioo ratio (1-ratio)) (cantorSet ratio) := by
  apply Set.disjoint_left.mpr
  rintro coordinate ⟨gap_coordinate, in_gap, rfl⟩ membership
  obtain ⟨cylinder, length_eq, tail, tail_mem, equation⟩ :=
    exists_scalar_cylinder positive.le (by linarith) (word.length+1) membership
  have depth_order : word.length ≤ cylinder.length := by omega
  have different : word ≠ cylinder := by
    intro equality
    rw [← equality] at length_eq
    omega
  exact scalar_gap_avoids_cylinder positive less_half word cylinder depth_order different in_gap
    (cantorSet_subset_unitInterval positive.le (by linarith) tail_mem) equation

end LambdaCantor.Last
