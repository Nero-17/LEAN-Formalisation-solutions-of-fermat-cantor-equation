import LambdaCantor.Last.AnalyticIsolatedPerfect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last

/-- Two distinct field-coordinate points on an affine level force the slope
to belong to the field. This algebraic fact uses no address classification. -/
theorem field_points_unique_in_external_slope
    (field : Subfield ℝ) {slope level : ℝ} (outside : slope ∉ field)
    {first second : ℝ × ℝ}
    (first_field : first.1 ∈ field ∧ first.2 ∈ field)
    (second_field : second.1 ∈ field ∧ second.2 ∈ field)
    (first_level : first.1 + slope * first.2 = level)
    (second_level : second.1 + slope * second.2 = level) : first = second := by
  have second_equal : first.2 = second.2 := by
    by_contra different
    apply outside
    have division_mem := field.div_mem (field.sub_mem second_field.1 first_field.1)
      (field.sub_mem first_field.2 second_field.2)
    have slope_eq : slope = (second.1-first.1)/(first.2-second.2) := by
      apply (eq_div_iff (sub_ne_zero.mpr different)).2
      nlinarith
    rw [slope_eq]
    exact division_mem
  apply Prod.ext
  · rw [second_equal] at first_level
    linarith
  · exact second_equal

/-- A compact affine fibre with field-coordinate isolated points is either
a singleton or uncountable when its slope is outside that field. -/
theorem affine_fibre_subsingleton_or_uncountable_over_field
    (field : Subfield ℝ) (fibre : Set (ℝ × ℝ)) (compact : IsCompact fibre)
    {slope level : ℝ} (outside : slope ∉ field)
    (on_level : ∀ point ∈ fibre, point.1 + slope * point.2 = level)
    (isolated_in_field : ∀ point : fibre, IsOpen ({point} : Set fibre) →
      point.val.1 ∈ field ∧ point.val.2 ∈ field) :
    fibre.Subsingleton ∨ ¬ fibre.Countable := by
  classical
  by_cases countable : fibre.Countable
  · left
    letI : Countable fibre := countable.to_subtype
    letI : CompleteSpace fibre := compact.isComplete.completeSpace_coe
    have subsingleton : Subsingleton fibre :=
      LambdaCantor.Integer.subsingleton_of_isolated_unique (by
        intro first second first_isolated second_isolated
        apply Subtype.ext
        exact field_points_unique_in_external_slope field outside
          (isolated_in_field first first_isolated) (isolated_in_field second second_isolated)
          (on_level first.val first.property) (on_level second.val second.property))
    intro first first_mem second second_mem
    exact congrArg Subtype.val (@Subsingleton.elim fibre subsingleton
      (⟨first, first_mem⟩ : fibre) (⟨second, second_mem⟩ : fibre))
  · exact Or.inr countable

theorem affine_fibre_two_points_uncountable_over_field
    (field : Subfield ℝ) (fibre : Set (ℝ × ℝ)) (compact : IsCompact fibre)
    {slope level : ℝ} (outside : slope ∉ field)
    (on_level : ∀ point ∈ fibre, point.1 + slope * point.2 = level)
    (isolated_in_field : ∀ point : fibre, IsOpen ({point} : Set fibre) →
      point.val.1 ∈ field ∧ point.val.2 ∈ field)
    {first second : ℝ × ℝ} (first_mem : first ∈ fibre) (second_mem : second ∈ fibre)
    (different : first ≠ second) : ¬ fibre.Countable := by
  rcases affine_fibre_subsingleton_or_uncountable_over_field field fibre compact
    outside on_level isolated_in_field with subsingleton | uncountable
  · exact False.elim (different (subsingleton first_mem second_mem))
  · exact uncountable

end LambdaCantor.Last
