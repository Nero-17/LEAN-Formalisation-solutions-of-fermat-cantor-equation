import LambdaCantor.Circle.ZeroWindowAccumulation
import LambdaCantor.Circle.OnsetConsequences

noncomputable section
namespace LambdaCantor.Circle

/-- An axis-only scalar statement identifies the shared real-exponent intersection. -/
theorem intersection_eq_axes_of_scalar {ratio : ℝ} (positive : 0 < ratio)
    (less_one : ratio < 1)
    (axis_only : ∀ x ∈ cantorSet ratio, ∀ y ∈ cantorSet ratio,
      x ^ 2 + y ^ 2 = 1 → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)) :
    intersection 2 ratio = ({(0, 1), (1, 0)} : Set (ℝ × ℝ)) := by
  ext point
  constructor
  · rintro ⟨first_mem, second_mem, equation⟩
    have natural_equation : point.1 ^ (2 : ℕ) + point.2 ^ (2 : ℕ) = 1 := by
      simpa only [Real.rpow_two] using equation
    have axis := axis_only point.1 first_mem point.2 second_mem natural_equation
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases axis with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inl (Prod.ext first second)
    · exact Or.inr (Prod.ext first second)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨zero_mem_cantorSet ratio, one_mem_cantorSet positive.le less_one, by norm_num⟩
    · exact ⟨one_mem_cantorSet positive.le less_one, zero_mem_cantorSet ratio, by norm_num⟩

/-- Zero Hausdorff-dimension open intervals accumulate immediately above
2 - sqrt 3, stated using the project's common intersection definition. -/
theorem zero_dimension_intervals_arbitrarily_close
    (epsilon : ℝ) (epsilon_positive : 0 < epsilon) :
    ∃ left right : ℝ, left < right ∧
      Set.Ioo left right ⊆ Set.Ioo onset (onset + epsilon) ∧
      ∀ ratio ∈ Set.Ioo left right, dimH (intersection 2 ratio) = 0 := by
  obtain ⟨left, right, ordered, subset, axes⟩ :=
    zero_intervals_arbitrarily_close (min epsilon (1 / 2)) (lt_min epsilon_positive (by norm_num))
  refine ⟨left, right, ordered, ?_, ?_⟩
  · intro ratio member
    have bounds := subset member
    have upper_near : onset + min epsilon (1 / 2 : ℝ) ≤ onset + epsilon := by
      linarith [min_le_left epsilon (1 / 2 : ℝ)]
    exact ⟨bounds.1, bounds.2.trans_le upper_near⟩
  · intro ratio member
    have bounds := subset member
    have positive : 0 < ratio := lt_trans onset_pos bounds.1
    have less_one : ratio < 1 := by
      have := onset_lt_one_third
      have := min_le_right epsilon (1 / 2 : ℝ)
      linarith [bounds.2]
    rw [intersection_eq_axes_of_scalar positive less_one (axes ratio member)]
    exact ((Set.finite_singleton ((1, 0) : ℝ × ℝ)).insert (0, 1)).dimH_zero

end LambdaCantor.Circle
