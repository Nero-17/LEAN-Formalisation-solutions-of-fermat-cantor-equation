import LambdaCantor.Last.AnalyticIsolatedMonotone
import LambdaCantor.Last.CylinderTopology

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem actual_cylinder_unique_child_hulls {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2) (slope_lower : 1 ≤ slope)
    (function : (ℝ × ℝ) → ℝ) (word : List (Bool × Bool)) (point : ℝ × ℝ)
    {bound : ℝ≥0} (bound_small : (bound : ℝ) ≤ 1)
    (error_lipschitz : LipschitzOnWith bound
      (fun value => function value-positiveLinearContinuous slope value) (wordCylinder ratio word))
    (outer : (1-2*ratio)*(1+(bound : ℝ)) < ratio*(slope-bound))
    (middle : (1-2*ratio)*(slope+(bound : ℝ)) < 1-bound)
    (singleton : ∀ other : ℝ × ℝ, other ∈ cantorDust ratio → function other = function point →
      other ∈ wordCylinder ratio word → other = point)
    (digit : Bool × Bool) (tail : ℝ × ℝ) (tail_mem : tail ∈ cantorDust ratio)
    (representation : wordMap ratio word (wordMap ratio [digit] tail) = point) :
    normalizedActualFunction function ratio word (wordMap ratio [digit] tail) ∈ Set.Icc
      (normalizedActualFunction function ratio word (wordMap ratio [digit] 0))
      (normalizedActualFunction function ratio word (wordMap ratio [digit] (1,1))) ∧
    ∀ other : Bool × Bool, other ≠ digit →
      normalizedActualFunction function ratio word (wordMap ratio [digit] tail) ∉ Set.Icc
        (normalizedActualFunction function ratio word (wordMap ratio [other] 0))
        (normalizedActualFunction function ratio word (wordMap ratio [other] (1,1))) := by
  have less_one : ratio < 1 := by linarith
  have scale_positive : 0 < ratio^word.length := pow_pos positive _
  have zero_mem : (0 : ℝ × ℝ) ∈ cantorDust ratio := ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩
  have one_mem : ((1,1) : ℝ × ℝ) ∈ cantorDust ratio :=
    ⟨one_mem_cantorSet positive.le less_one, one_mem_cantorSet positive.le less_one⟩
  have child_mem := wordMap_mem_dust positive.le less_one [digit] tail_mem
  have inside_word : wordMap ratio word (wordMap ratio [digit] tail) ∈ wordCylinder ratio word :=
    ⟨_, child_mem, rfl⟩
  have lower_mem : wordMap ratio word (wordMap ratio [digit] 0) ∈ wordCylinder ratio word :=
    ⟨_, wordMap_mem_dust positive.le less_one [digit] zero_mem, rfl⟩
  have upper_mem : wordMap ratio word (wordMap ratio [digit] (1,1)) ∈ wordCylinder ratio word :=
    ⟨_, wordMap_mem_dust positive.le less_one [digit] one_mem, rfl⟩
  have first_bounds := cantorSet_subset_unitInterval positive.le less_one tail_mem.1
  have second_bounds := cantorSet_subset_unitInterval positive.le less_one tail_mem.2
  have lower_order := wordMap_coordinate_order positive.le (word++[digit]) (first := 0) (second := tail)
    ⟨first_bounds.1, second_bounds.1⟩
  have upper_order := wordMap_coordinate_order positive.le (word++[digit]) (first := tail) (second := (1,1))
    ⟨first_bounds.2, second_bounds.2⟩
  simp only [wordMap_append] at lower_order upper_order
  have lower_value := actual_increasing_of_cylinder_error slope_lower function word bound_small
    error_lipschitz lower_mem inside_word lower_order
  have upper_value := actual_increasing_of_cylinder_error slope_lower function word bound_small
    error_lipschitz inside_word upper_mem upper_order
  constructor
  · constructor
    · exact (div_le_div_iff_of_pos_right scale_positive).mpr (sub_le_sub_right lower_value _)
    · exact (div_le_div_iff_of_pos_right scale_positive).mpr (sub_le_sub_right upper_value _)
  · intro other different other_brackets
    unfold normalizedActualFunction at other_brackets
    rw [representation] at other_brackets
    have raw_brackets : function point ∈ Set.Icc
        (function (wordMap ratio word (wordMap ratio [other] 0)))
        (function (wordMap ratio word (wordMap ratio [other] (1,1)))) := by
      constructor
      · have bound := (div_le_div_iff_of_pos_right scale_positive).mp other_brackets.1
        linarith
      · have bound := (div_le_div_iff_of_pos_right scale_positive).mp other_brackets.2
        linarith
    obtain ⟨other_tail, other_tail_mem, other_level⟩ := actual_child_hull_filled_of_cylinder_error
      positive less_half function word error_lipschitz outer middle other raw_brackets
    have other_child_mem := wordMap_mem_dust positive.le less_one [other] other_tail_mem
    have equal := singleton (wordMap ratio word (wordMap ratio [other] other_tail))
      (wordMap_mem_dust positive.le less_one word other_child_mem) other_level ⟨_, other_child_mem, rfl⟩
    have child_equal := wordMap_injective positive word (equal.trans representation.symm)
    have separated := first_digit_distance_gap positive.le less_one other digit different other_tail_mem tail_mem
    rw [child_equal, dist_self] at separated
    linarith

end LambdaCantor.Last
