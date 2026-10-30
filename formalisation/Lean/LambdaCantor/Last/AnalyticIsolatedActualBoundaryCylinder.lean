import LambdaCantor.Last.AnalyticIsolatedBoundaryModels

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

/-- The unique-child boundary estimate for one genuine actual cylinder.
Small actual residual error fills every other closed child hull, so isolation
excludes them; the actual hull comparison then gives the quantitative
exclusive-region estimate used by shadowing. -/
theorem actual_boundary_cylinder_exclusive {ratio : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (critical_equation : 2*ratio^2+2*ratio=1) (ratio_lower : (1/3 : ℝ) < ratio)
    (function : (ℝ × ℝ) → ℝ) (word : List (Bool × Bool)) (point : ℝ × ℝ)
    {bound : ℝ≥0} (bound_small : (bound : ℝ) ≤ 1/100)
    (error_lipschitz : LipschitzOnWith bound
      (fun value => function value-positiveLinearContinuous (1+ratio) value) (wordCylinder ratio word))
    (normalized_error : ∀ value ∈ cantorDust ratio,
      |normalizedActualFunction function ratio word value-positiveLinearContinuous (1+ratio) value| ≤ bound)
    (singleton : ∀ other : ℝ × ℝ, other ∈ cantorDust ratio → function other = function point →
      other ∈ wordCylinder ratio word → other = point)
    (digit : Bool × Bool) (tail : ℝ × ℝ) (tail_mem : tail ∈ cantorDust ratio)
    (representation : wordMap ratio word (wordMap ratio [digit] tail) = point) :
    BoundaryApproxExclusive ratio
      (positiveLinearContinuous (1+ratio) (wordMap ratio [digit] tail)) (2*(bound : ℝ)) digit := by
  have less_one : ratio < 1 := by linarith
  have scale_positive : 0 < ratio^word.length := pow_pos positive _
  let lower := fun child : Bool × Bool => normalizedActualFunction function ratio word (wordMap ratio [child] 0)
  let upper := fun child : Bool × Bool => normalizedActualFunction function ratio word (wordMap ratio [child] (1,1))
  let actualLevel := normalizedActualFunction function ratio word (wordMap ratio [digit] tail)
  have zero_in_dust : (0 : ℝ × ℝ) ∈ cantorDust ratio :=
    ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩
  have one_in_dust : ((1,1) : ℝ × ℝ) ∈ cantorDust ratio :=
    ⟨one_mem_cantorSet positive.le less_one, one_mem_cantorSet positive.le less_one⟩
  have lower_close : ∀ child, |lower child-boundaryAffineLower ratio child| ≤ (bound : ℝ) := by
    intro child
    rw [← (boundary_linear_child_endpoints critical_equation child).1]
    exact normalized_error _ (wordMap_mem_dust positive.le less_one [child] zero_in_dust)
  have upper_close : ∀ child, |upper child-boundaryAffineUpper ratio child| ≤ (bound : ℝ) := by
    intro child
    rw [← (boundary_linear_child_endpoints critical_equation child).2]
    exact normalized_error _ (wordMap_mem_dust positive.le less_one [child] one_in_dust)
  have ordered := boundary_child_hulls_ordered ratio_lower less_half bound_small lower upper lower_close upper_close
  have child_in_dust := wordMap_mem_dust positive.le less_one [digit] tail_mem
  have child_in_word : wordMap ratio word (wordMap ratio [digit] tail) ∈ wordCylinder ratio word :=
    ⟨_, child_in_dust, rfl⟩
  have lower_in_word : wordMap ratio word (wordMap ratio [digit] 0) ∈ wordCylinder ratio word :=
    ⟨_, wordMap_mem_dust positive.le less_one [digit] zero_in_dust, rfl⟩
  have upper_in_word : wordMap ratio word (wordMap ratio [digit] (1,1)) ∈ wordCylinder ratio word :=
    ⟨_, wordMap_mem_dust positive.le less_one [digit] one_in_dust, rfl⟩
  have tail_bounds := And.intro
    (cantorSet_subset_unitInterval positive.le less_one tail_mem.1)
    (cantorSet_subset_unitInterval positive.le less_one tail_mem.2)
  have lower_order := wordMap_coordinate_order positive.le (word++[digit])
    (first := 0) (second := tail) ⟨tail_bounds.1.1, tail_bounds.2.1⟩
  have upper_order := wordMap_coordinate_order positive.le (word++[digit])
    (first := tail) (second := (1,1)) ⟨tail_bounds.1.2, tail_bounds.2.2⟩
  simp only [wordMap_append] at lower_order upper_order
  have lower_value := actual_increasing_of_cylinder_error (show 1 ≤ 1+ratio by linarith)
    function word (show (bound : ℝ) ≤ 1 by linarith) error_lipschitz lower_in_word child_in_word lower_order
  have upper_value := actual_increasing_of_cylinder_error (show 1 ≤ 1+ratio by linarith)
    function word (show (bound : ℝ) ≤ 1 by linarith) error_lipschitz child_in_word upper_in_word upper_order
  have inside : actualLevel ∈ Set.Icc (lower digit) (upper digit) := by
    constructor
    · exact (div_le_div_iff_of_pos_right scale_positive).mpr (sub_le_sub_right lower_value _)
    · exact (div_le_div_iff_of_pos_right scale_positive).mpr (sub_le_sub_right upper_value _)
  have unique : ∀ other : Bool × Bool, other ≠ digit → actualLevel ∉ Set.Icc (lower other) (upper other) := by
    intro other different other_brackets
    have actual_brackets : function point ∈ Set.Icc
        (function (wordMap ratio word (wordMap ratio [other] 0)))
        (function (wordMap ratio word (wordMap ratio [other] (1,1)))) := by
      change (function (wordMap ratio word (wordMap ratio [digit] tail))-
        function (wordMap ratio word 0))/ratio^word.length ∈ Set.Icc _ _ at other_brackets
      rw [representation] at other_brackets
      constructor
      · have bound := (div_le_div_iff_of_pos_right scale_positive).mp other_brackets.1
        linarith
      · have bound := (div_le_div_iff_of_pos_right scale_positive).mp other_brackets.2
        linarith
    have margins := critical_weak_overlap_margins critical_equation ratio_lower less_half
      bound.coe_nonneg bound_small
    obtain ⟨other_tail, other_tail_mem, other_level⟩ := actual_child_hull_filled_of_cylinder_error
      positive less_half function word error_lipschitz margins.1 margins.2 other actual_brackets
    have other_child_mem := wordMap_mem_dust positive.le less_one [other] other_tail_mem
    have equal := singleton (wordMap ratio word (wordMap ratio [other] other_tail))
      (wordMap_mem_dust positive.le less_one word other_child_mem) other_level
      ⟨_, other_child_mem, rfl⟩
    have child_equal := wordMap_injective positive word (equal.trans representation.symm)
    have separated := first_digit_distance_gap positive.le less_one other digit different other_tail_mem tail_mem
    rw [child_equal, dist_self] at separated
    linarith
  apply boundary_approx_exclusive_of_actual_hulls lower upper ordered digit inside unique lower_close upper_close
  simpa [actualLevel, abs_sub_comm] using normalized_error _ child_in_dust

end LambdaCantor.Last
