import LambdaCantor.Circle.Onset

noncomputable section
namespace LambdaCantor.Circle

/-- The exact intersection statement below and at the circle onset, in the
shared `intersection` definition with real exponents. -/
theorem intersection_eq_axes {ratio : ℝ} (positive : 0 < ratio)
    (below_onset : ratio ≤ onset) :
    intersection 2 ratio = ({(0, 1), (1, 0)} : Set (ℝ × ℝ)) := by
  have less_one : ratio < 1 := lt_trans (lt_of_le_of_lt below_onset onset_lt_one_third) (by norm_num)
  ext point
  constructor
  · rintro ⟨first_mem, second_mem, equation⟩
    have natural_equation : point.1 ^ (2 : ℕ) + point.2 ^ (2 : ℕ) = 1 := by
      simpa only [Real.rpow_two] using equation
    have axis := circle_axis_only positive below_onset first_mem second_mem natural_equation
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases axis with ⟨first, second⟩ | ⟨first, second⟩
    · exact Or.inl (Prod.ext first second)
    · exact Or.inr (Prod.ext first second)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨zero_mem_cantorSet ratio, one_mem_cantorSet positive.le less_one, by norm_num⟩
    · exact ⟨one_mem_cantorSet positive.le less_one, zero_mem_cantorSet ratio, by norm_num⟩

theorem dimH_intersection_zero {ratio : ℝ} (positive : 0 < ratio)
    (below_onset : ratio ≤ onset) : dimH (intersection 2 ratio) = 0 := by
  rw [intersection_eq_axes positive below_onset]
  exact ((Set.finite_singleton ((1, 0) : ℝ × ℝ)).insert (0, 1)).dimH_zero

/-- The lower onset bound follows as soon as the positive-dimensional
parameter set is known nonempty. Its nonemptiness belongs to the separate
positive-measure construction and is not postulated here as an axiom. -/
theorem onset_le_firstTransition
    (nonempty_parameters : {ratio : ℝ | ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
      0 < dimH (intersection 2 ratio)}.Nonempty) : onset ≤ firstTransition 2 := by
  unfold firstTransition
  apply le_csInf nonempty_parameters
  intro ratio admissible
  by_contra below
  have dimension_zero := dimH_intersection_zero admissible.1.1 (le_of_lt (lt_of_not_ge below))
  have positive_dimension := admissible.2
  rw [dimension_zero] at positive_dimension
  exact (lt_irrefl 0) positive_dimension

end LambdaCantor.Circle
