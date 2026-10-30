import LambdaCantor.Common
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

noncomputable section

namespace LambdaCantor.First.Roots

/-- Comparison function used to construct the full-tail root families. -/
def comparison (exponent phase ratio : ℝ) : ℝ :=
  (1 - ratio) ^ exponent - exponent * ratio ^ phase

theorem comparison_strictAnti (exponent phase : ℝ)
    (exponent_pos : 0 < exponent) (phase_pos : 0 < phase) :
    StrictAntiOn (comparison exponent phase) (Set.Ioo 0 1) := by
  intro left left_mem right right_mem ordered
  have first := Real.rpow_lt_rpow (by linarith [right_mem.2] : 0 ≤ 1 - right)
    (by linarith : 1 - right < 1 - left) exponent_pos
  have second := Real.rpow_lt_rpow left_mem.1.le ordered phase_pos
  dsimp [comparison]
  nlinarith

/-- The phase chosen in the irrational construction is positive. -/
theorem chosen_phase_pos (exponent ratio : ℝ) (exponent_gt : 1 < exponent)
    (ratio_pos : 0 < ratio) (ratio_lt : ratio < 1) :
    0 < (exponent * Real.log (1 - ratio) - Real.log exponent) / Real.log ratio := by
  have log_ratio := Real.log_neg ratio_pos ratio_lt
  have log_complement := Real.log_neg (by linarith : 0 < 1 - ratio)
    (by linarith : 1 - ratio < 1)
  have log_exponent := Real.log_pos exponent_gt
  apply div_pos_of_neg_of_neg _ log_ratio
  nlinarith

/-- The chosen phase places the comparison root at the requested parameter. -/
theorem comparison_chosen_phase (exponent ratio : ℝ) (exponent_pos : 0 < exponent)
    (ratio_pos : 0 < ratio) (ratio_lt : ratio < 1) :
    comparison exponent
      ((exponent * Real.log (1 - ratio) - Real.log exponent) / Real.log ratio)
      ratio = 0 := by
  have log_ne : Real.log ratio ≠ 0 := (Real.log_neg ratio_pos ratio_lt).ne
  rw [comparison, Real.rpow_def_of_pos (by linarith : 0 < 1 - ratio),
    Real.rpow_def_of_pos ratio_pos]
  rw [mul_div_cancel₀ _ log_ne, Real.exp_sub, Real.exp_log exponent_pos]
  field_simp
  ring

/-- The pointwise estimate behind (root-tail), with the full error term retained.
Its integration only needs integrability of the square and the error. -/
theorem tail_pointwise (density kernel error threshold : ℝ)
    (threshold_pos : 0 < threshold) (kernel_nonneg : 0 ≤ kernel)
    (error_nonneg : 0 ≤ error) (dominated : density ≤ kernel + error)
    (large : threshold < density) :
    density ≤ 2 * kernel ^ 2 / threshold + 3 * error := by
  by_cases kernel_large : threshold / 2 < kernel
  · have square_bound : kernel ≤ 2 * kernel ^ 2 / threshold := by
      apply (le_div_iff₀ threshold_pos).2
      nlinarith
    linarith

  · have small : kernel ≤ threshold / 2 := le_of_not_gt kernel_large
    have error_large : threshold / 2 < error := by linarith
    have square_nonneg : 0 ≤ 2 * kernel ^ 2 / threshold :=
      div_nonneg (by positivity) threshold_pos.le
    linarith
/-- The density tail estimate used in the nonlinear root argument. This is valid
on an arbitrary measure space and does not presume that the root law has a density. -/
theorem density_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (measure : MeasureTheory.Measure Ω) (density kernel error : Ω → ℝ)
    (threshold : ℝ) (threshold_pos : 0 < threshold)
    (density_integrable : MeasureTheory.Integrable density measure)
    (square_integrable : MeasureTheory.Integrable (fun x => kernel x ^ 2) measure)
    (error_integrable : MeasureTheory.Integrable error measure)
    (tail_measurable : MeasurableSet {x | threshold < density x})
    (kernel_nonneg : ∀ x, 0 ≤ kernel x) (error_nonneg : ∀ x, 0 ≤ error x)
    (dominated : ∀ x, density x ≤ kernel x + error x) :
    ∫ x, ({x | threshold < density x}.indicator density) x ∂measure ≤
      2 / threshold * (∫ x, kernel x ^ 2 ∂measure) +
        3 * (∫ x, error x ∂measure) := by
  have majorant_integrable :=
    (square_integrable.const_mul (2 / threshold)).add (error_integrable.const_mul 3)
  calc
    _ ≤ ∫ x, (2 / threshold * kernel x ^ 2 + 3 * error x) ∂measure := by
      apply MeasureTheory.integral_mono
        (density_integrable.indicator tail_measurable) majorant_integrable
      intro x
      by_cases large : threshold < density x
      · rw [Set.indicator_of_mem (show x ∈ {x | threshold < density x} from large)]
        have bound := tail_pointwise (density x) (kernel x) (error x) threshold
          threshold_pos (kernel_nonneg x) (error_nonneg x) (dominated x) large
        change density x ≤ 2 / threshold * kernel x ^ 2 + 3 * error x
        calc
          density x ≤ 2 * kernel x ^ 2 / threshold + 3 * error x := bound
          _ = _ := by ring
      · rw [Set.indicator_of_notMem (show x ∉ {x | threshold < density x} from large)]
        exact add_nonneg (mul_nonneg (div_nonneg (by norm_num) threshold_pos.le)
          (sq_nonneg _)) (mul_nonneg (by norm_num) (error_nonneg x))
    _ = _ := by
      rw [MeasureTheory.integral_add (square_integrable.const_mul (2 / threshold))
        (error_integrable.const_mul 3), MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]


/-- A continuous strictly decreasing residual with opposite endpoint signs has
exactly one root, and that root is in the interior. -/
theorem unique_interior_root {residual : ℝ → ℝ} {left right : ℝ}
    (ordered : left < right)
    (continuous : ContinuousOn residual (Set.Icc left right))
    (decreasing : StrictAntiOn residual (Set.Icc left right))
    (left_sign : 0 < residual left) (right_sign : residual right < 0) :
    ∃! ratio, ratio ∈ Set.Ioo left right ∧ residual ratio = 0 := by
  obtain ⟨ratio, ratio_mem, root⟩ := intermediate_value_Icc' ordered.le continuous
    ⟨right_sign.le, left_sign.le⟩
  have left_ne : ratio ≠ left := by
    intro h
    subst ratio
    linarith
  have right_ne : ratio ≠ right := by
    intro h
    subst ratio
    linarith
  refine ⟨ratio, ⟨⟨lt_of_le_of_ne ratio_mem.1 (Ne.symm left_ne),
    lt_of_le_of_ne ratio_mem.2 right_ne⟩, root⟩, ?_⟩
  intro other other_root
  exact decreasing.injOn (Set.Ioo_subset_Icc_self other_root.1) ratio_mem
    (other_root.2.trans root.symm)

end LambdaCantor.First.Roots

