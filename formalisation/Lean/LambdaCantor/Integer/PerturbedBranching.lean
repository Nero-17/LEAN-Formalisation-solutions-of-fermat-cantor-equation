import LambdaCantor.Integer.AffineCoverage
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace LambdaCantor.Integer

noncomputable def childOffset (r : ℝ) (child : Fin 4) : ℝ :=
  match child.val with
  | 0 => 0
  | 1 => 1
  | 2 => r
  | _ => r+1

@[simp] theorem childOffset_zero (r : ℝ) : childOffset r 0 = 0 := rfl
@[simp] theorem childOffset_one (r : ℝ) : childOffset r 1 = 1 := rfl
@[simp] theorem childOffset_two (r : ℝ) : childOffset r 2 = r := rfl
@[simp] theorem childOffset_three (r : ℝ) : childOffset r 3 = r+1 := rfl

def approximateChildImage (r u error : ℝ) (child : Fin 4) : Prop :=
  childOffset r child / 3 - error ≤ u ∧
    u ≤ childOffset r child / 3 + (r+1)/6 + error

def expandedSwitchSet (r error : ℝ) : Set ℝ :=
  Set.Icc (1/3-error) ((r+1)/6+error) ∪
  Set.Icc (r/3-error) ((r+3)/6+error) ∪
  Set.Icc ((r+1)/3-error) ((3*r+1)/6+error)

def strictSwitchSet (r : ℝ) : Set ℝ :=
  Set.Ioo (1/3) ((r+1)/6) ∪
  Set.Ioo (r/3) ((r+3)/6) ∪
  Set.Ioo ((r+1)/3) ((3*r+1)/6)

/-- Two nonextreme child levels lie in an open switch overlap. This is the
algebraic step used after both selected children have uncountable fibres. -/
theorem strict_branching_in_switch (r u : ℝ) (positive : 1 < r)
    (first second : Fin 4) (different : first ≠ second)
    (firstImage : childOffset r first / 3 < u ∧
      u < childOffset r first / 3 + (r+1)/6)
    (secondImage : childOffset r second / 3 < u ∧
      u < childOffset r second / 3 + (r+1)/6) :
    u ∈ strictSwitchSet r := by
  unfold strictSwitchSet
  simp only [Set.mem_union, Set.mem_Ioo]
  fin_cases first <;> fin_cases second
  all_goals dsimp only [childOffset] at firstImage secondImage
  all_goals norm_num at firstImage secondImage
  all_goals norm_num at different
  all_goals first
    | (left; left; constructor <;> linarith [firstImage.1, firstImage.2,
        secondImage.1, secondImage.2])
    | (left; right; constructor <;> linarith [firstImage.1, firstImage.2,
        secondImage.1, secondImage.2])
    | (right; constructor <;> linarith [firstImage.1, firstImage.2,
        secondImage.1, secondImage.2])

/-- Two continuing children of a small perturbation force the normalized level
into the error-neighborhood of the switch intervals. Nonadjacent pairs are
excluded by their positive gap (r-1)/6, including both endpoint errors. -/
theorem branching_in_expanded_switch (r u error : ℝ) (positive : 1 < r)
    (small : 2*error < (r-1)/6) (first second : Fin 4)
    (different : first ≠ second)
    (firstImage : approximateChildImage r u error first)
    (secondImage : approximateChildImage r u error second) :
    u ∈ expandedSwitchSet r error := by
  unfold approximateChildImage at firstImage secondImage
  unfold expandedSwitchSet
  simp only [Set.mem_union, Set.mem_Icc]
  fin_cases first <;> fin_cases second
  all_goals dsimp only [childOffset] at firstImage secondImage
  all_goals norm_num at firstImage secondImage
  all_goals norm_num at different
  all_goals first
    | (left; left; constructor <;> linarith [firstImage.1, firstImage.2,
        secondImage.1, secondImage.2])
    | (left; right; constructor <;> linarith [firstImage.1, firstImage.2,
        secondImage.1, secondImage.2])
    | (right; constructor <;> linarith [firstImage.1, firstImage.2,
        secondImage.1, secondImage.2])

private theorem exists_close_interval (a b u error : ℝ) (ordered : a ≤ b)
    (nonnegative : 0 ≤ error) (approximate : a-error ≤ u ∧ u ≤ b+error) :
    ∃ v ∈ Set.Icc a b, |u-v| ≤ error := by
  by_cases left : u < a
  · refine ⟨a, ⟨le_rfl, ordered⟩, ?_⟩
    rw [abs_le]
    constructor <;> linarith [approximate.1, approximate.2]
  · by_cases right : b < u
    · refine ⟨b, ⟨ordered, le_rfl⟩, ?_⟩
      rw [abs_le]
      constructor <;> linarith [approximate.1, approximate.2]
    · exact ⟨u, ⟨le_of_not_gt left, le_of_not_gt right⟩, by simpa using nonnegative⟩

theorem expanded_switch_close (r u error : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (nonnegative : 0 ≤ error) (expanded : u ∈ expandedSwitchSet r error) :
    ∃ v ∈ switchSet r, |u-v| ≤ error := by
  rcases expanded with (first | second) | third
  · obtain ⟨v, hv, distance⟩ := exists_close_interval (1/3) ((r+1)/6) u error
      (by linarith) nonnegative first
    exact ⟨v, Or.inl (Or.inl hv), distance⟩
  · obtain ⟨v, hv, distance⟩ := exists_close_interval (r/3) ((r+3)/6) u error
      (by linarith) nonnegative second
    exact ⟨v, Or.inl (Or.inr hv), distance⟩
  · obtain ⟨v, hv, distance⟩ := exists_close_interval ((r+1)/3) ((3*r+1)/6) u error
      (by linarith) nonnegative third
    exact ⟨v, Or.inr hv, distance⟩

end LambdaCantor.Integer
