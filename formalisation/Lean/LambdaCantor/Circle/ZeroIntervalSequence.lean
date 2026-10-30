import LambdaCantor.Circle.ZeroDimensionIntervals
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Choose

noncomputable section
open Filter Topology
namespace LambdaCantor.Circle

/-- A sequence of genuine open axis-only windows, with their suprema tending
to the circle onset. This is the sequence formulation in the manuscript. -/
theorem circle_zero_intervals :
    ∃ intervals : ℕ → Set ℝ,
      (∀ index, IsOpen (intervals index) ∧ Set.OrdConnected (intervals index) ∧
        (intervals index).Nonempty ∧
        intervals index ⊆ Set.Ioo onset (1 / 2 : ℝ) ∧
        ∀ ratio ∈ intervals index,
          intersection 2 ratio = ({(0, 1), (1, 0)} : Set (ℝ × ℝ))) ∧
      Tendsto (fun index => sSup (intervals index)) atTop (𝓝 onset) := by
  have gap_positive : 0 < (1 / 2 : ℝ) - onset := by linarith [onset_lt_one_third]
  have window_exists (index : ℕ) : ∃ left right : ℝ, left < right ∧
      Set.Ioo left right ⊆ Set.Ioo onset
        (onset + ((1 / 2 : ℝ) - onset) / ((index : ℝ) + 1)) ∧
      ∀ ratio ∈ Set.Ioo left right, ∀ x ∈ cantorSet ratio, ∀ y ∈ cantorSet ratio,
        x ^ 2 + y ^ 2 = 1 → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) :=
    zero_intervals_arbitrarily_close _ (div_pos gap_positive (by positivity))
  choose left right ordered subset axes using window_exists
  have window_upper (index : ℕ) :
      onset + ((1 / 2 : ℝ) - onset) / ((index : ℝ) + 1) ≤ 1 / 2 := by
    have quotient_bound : ((1 / 2 : ℝ) - onset) / ((index : ℝ) + 1) ≤ (1 / 2 : ℝ) - onset := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (index : ℝ) + 1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) index]
    linarith
  refine ⟨fun index => Set.Ioo (left index) (right index), ?_, ?_⟩
  · intro index
    refine ⟨isOpen_Ioo, inferInstance, Set.nonempty_Ioo.mpr (ordered index), ?_, ?_⟩
    · intro ratio member
      exact ⟨(subset index member).1, (subset index member).2.trans_le (window_upper index)⟩
    · intro ratio member
      have positive := onset_pos.trans (subset index member).1
      have less_one : ratio < 1 := ((subset index member).2.trans_le (window_upper index)).trans (by norm_num)
      exact intersection_eq_axes_of_scalar positive less_one (axes index ratio member)
  · have upper_tendsto : Tendsto
        (fun index : ℕ => onset + ((1 / 2 : ℝ) - onset) / ((index : ℝ) + 1)) atTop (𝓝 onset) := by
      have reciprocal_limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        ((1 / 2 : ℝ) - onset)
      have constant_limit : Tendsto (fun _ : ℕ => onset) atTop (𝓝 onset) := tendsto_const_nhds
      simpa only [mul_one_div, mul_zero, add_zero] using constant_limit.add reciprocal_limit
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds upper_tendsto
    · intro index
      change onset ≤ sSup (Set.Ioo (left index) (right index))
      rw [csSup_Ioo (ordered index)]
      exact ((Set.Ioo_subset_Ioo_iff (ordered index)).mp (subset index)).1.trans (ordered index).le
    · intro index
      change sSup (Set.Ioo (left index) (right index)) ≤
        onset + ((1 / 2 : ℝ) - onset) / ((index : ℝ) + 1)
      rw [csSup_Ioo (ordered index)]
      exact ((Set.Ioo_subset_Ioo_iff (ordered index)).mp (subset index)).2

end LambdaCantor.Circle
