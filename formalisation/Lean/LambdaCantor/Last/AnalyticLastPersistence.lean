import LambdaCantor.Last.Transitions

noncomputable section
open scoped Topology
namespace LambdaCantor.Last

/-- A source that persists to the left of a positive terminal threshold gives
a strict last-transition bound, once the entire upper interval is positive. -/
theorem lastTransition_lt_of_positive_left_persistence {exponent bound radius : ℝ}
    (hbound : 0 < bound) (hradius : 0 < radius)
    (hleft : ∀ ratio ∈ Set.Ioo (bound - radius) bound,
      0 < dimH (intersection exponent ratio))
    (habove : ∀ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2), bound ≤ ratio →
      0 < dimH (intersection exponent ratio)) :
    lastTransition exponent < bound := by
  have hcutoff : max 0 (bound - radius / 2) < bound := max_lt hbound (by linarith)
  apply (lastTransition_le_of_nonnegative_bound (le_max_left 0 (bound - radius / 2)) ?_).trans_lt hcutoff
  intro ratio hratio habove_cutoff
  by_cases hbelow : ratio < bound
  · apply hleft ratio
    exact ⟨by linarith [le_max_right 0 (bound - radius / 2)], hbelow⟩
  · exact habove ratio hratio (le_of_not_gt hbelow)

theorem lastTransition_lt_of_positive_neighborhood {exponent bound : ℝ}
    (hbound : 0 < bound)
    (hneighborhood : ∀ᶠ ratio in 𝓝 bound, 0 < dimH (intersection exponent ratio))
    (habove : ∀ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2), bound ≤ ratio →
      0 < dimH (intersection exponent ratio)) :
    lastTransition exponent < bound := by
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  apply lastTransition_lt_of_positive_left_persistence hbound hradius _ habove
  intro ratio hratio
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hratio.2)]
  linarith [hratio.1]

end LambdaCantor.Last
