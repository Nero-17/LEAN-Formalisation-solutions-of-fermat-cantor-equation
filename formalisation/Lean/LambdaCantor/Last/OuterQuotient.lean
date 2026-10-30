import LambdaCantor.SelfSimilarity
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last

/-- The actual upper first-generation copy of the canonical Cantor set. -/
def outerCantor (ratio : ℝ) : Set ℝ :=
  (fun coordinate => 1-ratio+ratio*coordinate) '' cantorSet ratio

def outerQuotients (ratio : ℝ) : Set ℝ :=
  {quotient | ∃ numerator ∈ outerCantor ratio, ∃ denominator ∈ outerCantor ratio,
    quotient = numerator / denominator}

theorem isCompact_outerCantor {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : IsCompact (outerCantor ratio) :=
  (isCompact_cantorSet nonnegative less_one).image (by fun_prop)

theorem lower_mem_outerCantor (ratio : ℝ) : 1-ratio ∈ outerCantor ratio := by
  exact ⟨0, zero_mem_cantorSet ratio, by simp⟩

theorem one_mem_outerCantor {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : 1 ∈ outerCantor ratio := by
  exact ⟨1, one_mem_cantorSet nonnegative less_one, by ring⟩

theorem outerCantor_bounds {ratio coordinate : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) (membership : coordinate ∈ outerCantor ratio) :
    1-ratio ≤ coordinate ∧ coordinate ≤ 1 := by
  rcases membership with ⟨tail, tail_mem, rfl⟩
  have bounds := cantorSet_subset_unitInterval nonnegative less_one tail_mem
  constructor <;> nlinarith [mul_nonneg nonnegative bounds.1,
    mul_le_mul_of_nonneg_left bounds.2 nonnegative]

theorem outerCantor_subset_cantorSet {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : outerCantor ratio ⊆ cantorSet ratio := by
  rw [cantorSet_selfsimilar nonnegative less_one]
  exact Set.subset_union_right

theorem outerCantor_eq_upper_branch {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_half : ratio < 1/2) :
    outerCantor ratio = cantorSet ratio ∩ Set.Icc (1-ratio) 1 := by
  have less_one : ratio < 1 := by linarith
  apply Set.Subset.antisymm
  · intro coordinate membership
    exact ⟨outerCantor_subset_cantorSet nonnegative less_one membership,
      outerCantor_bounds nonnegative less_one membership⟩
  · rintro coordinate ⟨membership, bounds⟩
    rw [cantorSet_selfsimilar nonnegative less_one] at membership
    rcases membership with lower_membership | upper_membership
    · rcases lower_membership with ⟨tail, tail_mem, rfl⟩
      have tail_upper := (cantorSet_subset_unitInterval nonnegative less_one tail_mem).2
      have scaled_upper := mul_le_mul_of_nonneg_left tail_upper nonnegative
      exfalso
      nlinarith [bounds.1]
    · exact upper_membership

theorem outerQuotients_subset {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) : outerQuotients ratio ⊆ Set.Icc (1-ratio) (1-ratio)⁻¹ := by
  rintro quotient ⟨numerator, numerator_mem, denominator, denominator_mem, rfl⟩
  have numerator_bounds := outerCantor_bounds nonnegative less_one numerator_mem
  have denominator_bounds := outerCantor_bounds nonnegative less_one denominator_mem
  have denominator_positive : 0 < denominator := by linarith
  have lower_positive : 0 < 1-ratio := by linarith
  constructor
  · apply (le_div_iff₀ denominator_positive).mpr
    exact (mul_le_mul_of_nonneg_left denominator_bounds.2 lower_positive.le).trans
      (by simpa using numerator_bounds.1)
  · rw [inv_eq_one_div]
    apply (div_le_div_iff₀ denominator_positive lower_positive).mpr
    nlinarith [mul_le_mul_of_nonneg_right numerator_bounds.2 lower_positive.le]

theorem outerQuotients_endpoints {ratio : ℝ} (nonnegative : 0 ≤ ratio)
    (less_one : ratio < 1) :
    1-ratio ∈ outerQuotients ratio ∧ (1-ratio)⁻¹ ∈ outerQuotients ratio := by
  constructor
  · exact ⟨1-ratio, lower_mem_outerCantor ratio, 1,
      one_mem_outerCantor nonnegative less_one, by simp⟩
  · exact ⟨1, one_mem_outerCantor nonnegative less_one, 1-ratio,
      lower_mem_outerCantor ratio, by simp⟩

/-- The hulls [1-ratio,1] and [q(1-ratio),q] overlap strictly.
The last two inequalities compare hull lengths with the candidate largest gaps;
identifying these as the actual largest gaps is a separate obligation. -/
theorem outer_linked_hull_inequalities {ratio quotient : ℝ}
    (ratio_positive : 0 < ratio) (ratio_less_half : ratio < 1/2)
    (quotient_lower : 1-ratio < quotient)
    (quotient_upper : quotient < (1-ratio)⁻¹) :
    0 < quotient ∧ 1-ratio < quotient ∧ quotient*(1-ratio) < 1 ∧
      ratio*(1-2*ratio) < quotient*ratio ∧
      quotient*ratio*(1-2*ratio) < ratio := by
  have lower_positive : 0 < 1-ratio := by linarith
  have quotient_positive : 0 < quotient := by linarith
  have upper_product : quotient*(1-ratio) < 1 := by
    rw [inv_eq_one_div] at quotient_upper
    exact (lt_div_iff₀ lower_positive).mp quotient_upper
  refine ⟨quotient_positive, quotient_lower, upper_product, ?_, ?_⟩
  · nlinarith [mul_lt_mul_of_pos_right (show 1-2*ratio < quotient by linarith)
      ratio_positive]
  · have smaller_product : quotient*(1-2*ratio) < 1 := by
      nlinarith [mul_pos quotient_positive ratio_positive]
    nlinarith [mul_lt_mul_of_pos_right smaller_product ratio_positive]

/-- Explicit remaining gap-lemma interface, not an axiom. A geometric proof of
the intersection hypothesis yields the missing quotient inclusion. -/
theorem outerQuotient_of_intersection {ratio quotient : ℝ}
    (ratio_nonnegative : 0 ≤ ratio) (ratio_less_one : ratio < 1)
    (intersection_nonempty :
      (outerCantor ratio ∩ (fun coordinate => quotient*coordinate) '' outerCantor ratio).Nonempty) :
    quotient ∈ outerQuotients ratio := by
  obtain ⟨numerator, numerator_mem, denominator, denominator_mem, equation⟩ := intersection_nonempty
  have denominator_positive : 0 < denominator := by
    have := (outerCantor_bounds ratio_nonnegative ratio_less_one denominator_mem).1
    linarith
  refine ⟨numerator, numerator_mem, denominator, denominator_mem, ?_⟩
  exact (eq_div_iff denominator_positive.ne').mpr equation

theorem outerQuotients_eq_of_intersections {ratio : ℝ}
    (ratio_nonnegative : 0 ≤ ratio) (ratio_less_one : ratio < 1)
    (interior_intersections : ∀ quotient ∈ Set.Ioo (1-ratio) (1-ratio)⁻¹,
      (outerCantor ratio ∩ (fun coordinate => quotient*coordinate) '' outerCantor ratio).Nonempty) :
    outerQuotients ratio = Set.Icc (1-ratio) (1-ratio)⁻¹ := by
  apply Set.Subset.antisymm (outerQuotients_subset ratio_nonnegative ratio_less_one)
  intro quotient bounds
  rcases eq_or_lt_of_le bounds.1 with equality | lower_strict
  · rw [← equality]
    exact (outerQuotients_endpoints ratio_nonnegative ratio_less_one).1
  rcases eq_or_lt_of_le bounds.2 with equality | upper_strict
  · rw [equality]
    exact (outerQuotients_endpoints ratio_nonnegative ratio_less_one).2
  exact outerQuotient_of_intersection ratio_nonnegative ratio_less_one
    (interior_intersections quotient ⟨lower_strict, upper_strict⟩)

end LambdaCantor.Last
