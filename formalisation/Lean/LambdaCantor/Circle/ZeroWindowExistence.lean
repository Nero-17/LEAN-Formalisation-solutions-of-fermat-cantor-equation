import LambdaCantor.Circle.ZeroIntervalShells
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

noncomputable section
namespace LambdaCantor.Circle

 theorem onset_in_certificate_interval :
    (2679 / 10000 : ℝ) < onset ∧ onset < (67 / 250 : ℝ) := by
  have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have := Real.sqrt_nonneg (3 : ℝ)
  dsimp [onset]
  constructor <;> nlinarith

/-- Every sufficiently fine polynomial window has an interior centre. -/
theorem zero_window_centre (depth : ℕ) (depth_large : 3 ≤ depth) :
    ∃ ratio ∈ Set.Ioo onset (67 / 250 : ℝ),
      4 * ratio - 1 - ratio ^ 2 = (19 / 5 : ℝ) * ratio ^ (2 * depth + 2) := by
  have exponent_large : 8 ≤ 2 * depth + 2 := by omega
  have power_bound := power_antitone (by norm_num : (0 : ℝ) ≤ 67 / 250)
    (by norm_num : (67 / 250 : ℝ) ≤ 1) exponent_large
  have right_positive : 0 < 4 * (67 / 250 : ℝ) - 1 - (67 / 250 : ℝ) ^ 2 -
      (19 / 5 : ℝ) * (67 / 250 : ℝ) ^ (2 * depth + 2) := by
    norm_num at power_bound ⊢
    linarith
  have left_negative : 4 * onset - 1 - onset ^ 2 -
      (19 / 5 : ℝ) * onset ^ (2 * depth + 2) < 0 := by
    have := onset_equation
    have := pow_pos onset_pos (2 * depth + 2)
    nlinarith
  have continuous_residual : Continuous (fun ratio : ℝ =>
      4 * ratio - 1 - ratio ^ 2 - (19 / 5 : ℝ) * ratio ^ (2 * depth + 2)) := by fun_prop
  obtain ⟨ratio, bounds, equation⟩ := intermediate_value_Icc
    onset_in_certificate_interval.2.le continuous_residual.continuousOn
    (show (0 : ℝ) ∈ Set.Icc
      (4 * onset - 1 - onset ^ 2 - (19 / 5 : ℝ) * onset ^ (2 * depth + 2))
      (4 * (67 / 250 : ℝ) - 1 - (67 / 250 : ℝ) ^ 2 -
        (19 / 5 : ℝ) * (67 / 250 : ℝ) ^ (2 * depth + 2)) from
      ⟨left_negative.le, right_positive.le⟩)
  refine ⟨ratio, ⟨?_, ?_⟩, ?_⟩
  · exact lt_of_le_of_ne bounds.1 (by intro equality; subst ratio; linarith)
  · exact lt_of_le_of_ne bounds.2 (by intro equality; subst ratio; linarith)
  · linarith

/-- The open polynomial window is nonempty; all of its Cantor-circle points
are axes. This is independent of the positive-measure root construction. -/
theorem exists_open_zero_window (depth : ℕ) (depth_large : 3 ≤ depth) :
    ∃ left right : ℝ, left < right ∧
      Set.Ioo left right ⊆ Set.Ioo onset (67 / 250 : ℝ) ∧
      ∀ ratio ∈ Set.Ioo left right, ∀ x ∈ cantorSet ratio, ∀ y ∈ cantorSet ratio,
        x ^ 2 + y ^ 2 = 1 → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  have open_window : IsOpen {ratio : ℝ | ratio ∈ Set.Ioo onset (67 / 250 : ℝ) ∧
      (379 / 100 : ℝ) * ratio ^ (2 * depth + 2) < 4 * ratio - 1 - ratio ^ 2 ∧
      4 * ratio - 1 - ratio ^ 2 < (381 / 100 : ℝ) * ratio ^ (2 * depth + 2)} := by
    exact isOpen_Ioo.inter ((isOpen_lt
      (f := fun ratio : ℝ => (379 / 100 : ℝ) * ratio ^ (2 * depth + 2))
      (g := fun ratio : ℝ => 4 * ratio - 1 - ratio ^ 2)
      (by fun_prop) (by fun_prop)).inter
      (isOpen_lt
        (f := fun ratio : ℝ => 4 * ratio - 1 - ratio ^ 2)
        (g := fun ratio : ℝ => (381 / 100 : ℝ) * ratio ^ (2 * depth + 2))
        (by fun_prop) (by fun_prop)))
  obtain ⟨centre, centre_bounds, centre_equation⟩ := zero_window_centre depth depth_large
  have centre_power : 0 < centre ^ (2 * depth + 2) :=
    pow_pos (lt_trans onset_pos centre_bounds.1) _
  obtain ⟨left, right, ordered, subset⟩ := open_window.exists_Ioo_subset
    ⟨centre, centre_bounds, by rw [centre_equation]; nlinarith,
      by rw [centre_equation]; nlinarith⟩
  refine ⟨left, right, ordered, fun ratio member => (subset member).1, ?_⟩
  intro ratio member x x_mem y y_mem equation
  have conditions := subset member
  exact circle_axis_only_in_zero_window depth depth_large
    (le_trans onset_in_certificate_interval.1.le conditions.1.1.le)
    conditions.1.2.le conditions.2.1 conditions.2.2 x_mem y_mem equation

end LambdaCantor.Circle
