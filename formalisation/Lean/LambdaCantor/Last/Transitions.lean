import LambdaCantor.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace LambdaCantor

/-- The defining positive-dimension parameter set is bounded below. -/
theorem positiveParameters_bddBelow (exponent : ℝ) :
    BddBelow {ratio | ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
      0 < dimH (intersection exponent ratio)} := by
  exact ⟨0, fun _ h => le_of_lt h.1.1⟩

/-- The defining zero-dimension parameter set is bounded above. -/
theorem zeroParameters_bddAbove (exponent : ℝ) :
    BddAbove {ratio | ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
      dimH (intersection exponent ratio) = 0} := by
  exact ⟨1 / 2, fun _ h => h.1.2⟩

/-- A positive-dimensional parameter bounds the first transition from above. -/
theorem firstTransition_le_of_positive {exponent ratio : ℝ}
    (hratio : ratio ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hpositive : 0 < dimH (intersection exponent ratio)) :
    firstTransition exponent ≤ ratio := by
  exact csInf_le (positiveParameters_bddBelow exponent) ⟨hratio, hpositive⟩

/-- A zero-dimensional parameter bounds the last transition from below. -/
theorem le_lastTransition_of_zero {exponent ratio : ℝ}
    (hratio : ratio ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hzero : dimH (intersection exponent ratio) = 0) :
    ratio ≤ lastTransition exponent := by
  exact le_csSup (zeroParameters_bddAbove exponent) ⟨hratio, hzero⟩

/-- Positivity strictly above a bound supplies the corresponding last-transition bound.
Nonemptiness is explicit: the supremum of the empty set in ℝ is not used. -/
theorem lastTransition_le_of_positive_above {exponent bound : ℝ}
    (hzero : ∃ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2),
      dimH (intersection exponent ratio) = 0)
    (hpositive : ∀ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2),
      bound < ratio → 0 < dimH (intersection exponent ratio)) :
    lastTransition exponent ≤ bound := by
  apply csSup_le
  · obtain ⟨ratio, hratio, hdim⟩ := hzero
    exact ⟨ratio, hratio, hdim⟩
  · intro ratio hratio
    by_contra h
    have hp := hpositive ratio hratio.1 (lt_of_not_ge h)
    simpa [hratio.2] using hp

/-- Two parameters of opposite dimension types give strict separation. -/
theorem firstTransition_lt_lastTransition_of_witnesses
    {exponent positiveRatio zeroRatio : ℝ}
    (hpositiveRatio : positiveRatio ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hzeroRatio : zeroRatio ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (hpositive : 0 < dimH (intersection exponent positiveRatio))
    (hzero : dimH (intersection exponent zeroRatio) = 0)
    (horder : positiveRatio < zeroRatio) :
    firstTransition exponent < lastTransition exponent := by
  exact lt_of_le_of_lt (firstTransition_le_of_positive hpositiveRatio hpositive)
    (lt_of_lt_of_le horder (le_lastTransition_of_zero hzeroRatio hzero))

/-- A strict interior zero interval puts its central parameter strictly below the last transition. -/
theorem lt_lastTransition_of_zero_right_neighborhood {exponent ratio radius : ℝ}
    (hratio : 0 < ratio) (hradius : 0 < radius) (hbound : ratio + radius ≤ 1 / 2)
    (hzero : ∀ parameter ∈ Set.Ioo ratio (ratio + radius),
      dimH (intersection exponent parameter) = 0) :
    ratio < lastTransition exponent := by
  have hmid : ratio + radius / 2 ∈ Set.Ioo ratio (ratio + radius) := by
    constructor <;> linarith
  have hparam : ratio + radius / 2 ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    constructor <;> linarith [hmid.1, hmid.2]
  exact lt_of_lt_of_le hmid.1 (le_lastTransition_of_zero hparam (hzero _ hmid))

/-- A nonnegative upper bound also handles the empty zero-parameter set. -/
theorem lastTransition_le_of_nonnegative_bound {exponent bound : ℝ}
    (hbound : 0 ≤ bound)
    (hpositive : ∀ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2),
      bound < ratio → 0 < dimH (intersection exponent ratio)) :
    lastTransition exponent ≤ bound := by
  by_cases hzero : ∃ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2),
      dimH (intersection exponent ratio) = 0
  · exact lastTransition_le_of_positive_above hzero hpositive
  · have hempty : {ratio | ratio ∈ Set.Ioc (0 : ℝ) (1 / 2) ∧
        dimH (intersection exponent ratio) = 0} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ratio hratio
      exact hzero ⟨ratio, hratio.1, hratio.2⟩
    simpa only [lastTransition, hempty, Real.sSup_empty] using hbound

/-- Positivity on a terminal interval proves a nontrivial last transition.
This conclusion does not require an independent zero-dimensional witness. -/
theorem lastTransition_lt_half_of_positive_near_half {exponent bound : ℝ}
    (hbound : bound < 1 / 2)
    (hpositive : ∀ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2),
      bound < ratio → 0 < dimH (intersection exponent ratio)) :
    lastTransition exponent < 1 / 2 := by
  have hupper := lastTransition_le_of_nonnegative_bound (exponent := exponent)
    (bound := max 0 bound) (le_max_left _ _)
    (fun ratio hratio hlt => hpositive ratio hratio ((le_max_right _ _).trans_lt hlt))
  exact hupper.trans_lt (max_lt (by norm_num) hbound)
end LambdaCantor


