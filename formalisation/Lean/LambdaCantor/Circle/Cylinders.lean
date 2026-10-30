import LambdaCantor.Circle.Onset

noncomputable section
namespace LambdaCantor.Circle

theorem scaled_mem_cantorSet {ratio coordinate : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (membership : coordinate ∈ cantorSet ratio) (depth : ℕ) :
    ratio ^ depth * coordinate ∈ cantorSet ratio := by
  induction depth with
  | zero => simpa using membership
  | succ depth inductionHypothesis =>
      rcases inductionHypothesis with ⟨digits, equality⟩
      refine ⟨prependDigit false digits, ?_⟩
      simp only [address_prepend nonnegative less_one, Bool.false_eq_true, if_false,
        mul_zero, zero_add, equality, pow_succ]
      ring

/-- A point below the first forbidden digit must lie in the leftmost depth
`depth` cylinder; this is proved from the actual address, not an interval model. -/
theorem exists_leftmost_cylinder {ratio coordinate : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1)
    (membership : coordinate ∈ cantorSet ratio) (depth : ℕ) (depth_positive : 0 < depth)
    (small : coordinate < (1 - ratio) * ratio ^ (depth - 1)) :
    ∃ tail ∈ cantorSet ratio, coordinate = ratio ^ depth * tail := by
  by_cases zero : coordinate = 0
  · exact ⟨0, zero_mem_cantorSet ratio, by simp [zero]⟩
  obtain ⟨shellDepth, tail, tail_mem, tail_lower, tail_upper, shell⟩ :=
    exists_near_axis_shell positive less_one membership zero
  have depth_le : depth ≤ shellDepth := by
    by_contra contrary
    have shell_le : shellDepth ≤ depth - 1 := by omega
    have power_bound := power_antitone positive.le less_one.le shell_le
    have lower_bound : (1 - ratio) * ratio ^ (depth - 1) ≤ coordinate := by
      calc
        _ ≤ (1 - ratio) * ratio ^ shellDepth :=
          mul_le_mul_of_nonneg_left power_bound (by linarith)
        _ ≤ ratio ^ shellDepth * tail := by
          nlinarith [mul_nonneg (pow_nonneg positive.le shellDepth) (sub_nonneg.mpr tail_lower)]
        _ = coordinate := shell.symm
    linarith
  obtain ⟨remainingDepth, depth_equality⟩ := Nat.exists_eq_add_of_le depth_le
  refine ⟨ratio ^ remainingDepth * tail,
    scaled_mem_cantorSet positive.le less_one tail_mem remainingDepth, ?_⟩
  rw [shell, depth_equality, pow_add]
  ring

theorem exists_rightmost_cylinder {ratio coordinate : ℝ}
    (positive : 0 < ratio) (less_one : ratio < 1)
    (membership : coordinate ∈ cantorSet ratio) (depth : ℕ) (depth_positive : 0 < depth)
    (small : 1 - coordinate < (1 - ratio) * ratio ^ (depth - 1)) :
    ∃ tail ∈ cantorSet ratio, coordinate = 1 - ratio ^ depth * tail := by
  obtain ⟨tail, tail_mem, equality⟩ := exists_leftmost_cylinder positive less_one
    (one_sub_mem_cantorSet positive.le less_one membership) depth depth_positive small
  exact ⟨tail, tail_mem, by linarith⟩

theorem exists_outer_right_tail {ratio coordinate : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1 / 2)
    (membership : coordinate ∈ cantorSet ratio) (outer : 1 - ratio ≤ coordinate) :
    ∃ tail ∈ cantorSet ratio, coordinate = 1 - ratio + ratio * tail := by
  have less_one : ratio < 1 := by linarith
  rw [cantorSet_selfsimilar positive.le less_one] at membership
  rcases membership with ⟨tail, tail_mem, equality⟩ | ⟨tail, tail_mem, equality⟩
  · have bounds := cantorSet_subset_unitInterval positive.le less_one tail_mem
    have : ratio * tail ≤ ratio := by nlinarith [bounds.2]
    exfalso
    linarith
  · exact ⟨tail, tail_mem, equality.symm⟩

end LambdaCantor.Circle
