import LambdaCantor.Last.ActualSectionFour
import LambdaCantor.Manuscript.AverageSobolev
import Mathlib.NumberTheory.Real.Irrational

/-! Independently compilable introduction/Section4 wrappers for manuscript
429d53b. This entry consumes the actual Last/AE/Circle endpoints and imports
no middle-third rational source catalogue or partition production. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LambdaCantor.Manuscript

/-- Theorem 1.3, the introduction's strict universal last bound. -/
theorem introductory_last_transition {exponent : ℝ} (above_one : 1 < exponent) :
    lastTransition exponent < (Real.sqrt 3-1)/2 :=
  Last.universal_lastTransition_lt_critical above_one

/-- Theorem 1.4, identical to the later a.e. dimension assertion. -/
theorem introductory_ae_dimension {exponent : ℝ}
    (irrational : Irrational exponent) (above_one : 1 < exponent) :
    ∀ᵐ ratio : ℝ, ratio ∈ Set.Ioo (Real.sqrt 3/4) (1/2) →
      dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio) :=
  AE.irrational_ae_dimension_equality irrational above_one

theorem expectedDimension_strictly_increasing {first second : ℝ}
    (first_positive : 0 < first) (ordered : first < second) (second_below_one : second < 1) :
    expectedDimension first < expectedDimension second := by
  have second_positive : 0 < second := first_positive.trans ordered
  have first_below_one : first < 1 := ordered.trans second_below_one
  have first_log_positive : 0 < Real.log (1/first) :=
    Real.log_pos ((lt_div_iff₀ first_positive).mpr (by simpa using first_below_one))
  have second_log_positive : 0 < Real.log (1/second) :=
    Real.log_pos ((lt_div_iff₀ second_positive).mpr (by simpa using second_below_one))
  have reciprocal_order : 1/second < 1/first :=
    (div_lt_div_iff₀ second_positive first_positive).mpr (by simpa using ordered)
  have logarithm_order := Real.log_lt_log (by positivity : 0 < 1/second) reciprocal_order
  have numerator_positive : 0 < 2*Real.log 2 :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  unfold expectedDimension
  exact sub_lt_sub_right
    ((div_lt_div_iff₀ first_log_positive second_log_positive).mpr
      (mul_lt_mul_of_pos_left logarithm_order numerator_positive)) 1

/-- Example 4.9, including the explicit sqrt(2) exponent, parameter window,
and both strict numerical dimension bounds. -/
theorem ae_sqrt_two_dimension_bounds :
    ∀ᵐ ratio : ℝ, ratio ∈ Set.Ioo (7/16 : ℝ) (9/20) →
      ENNReal.ofReal (2*Real.log 2/Real.log (16/7 : ℝ)-1) <
          dimH (intersection (Real.sqrt 2) ratio) ∧
      dimH (intersection (Real.sqrt 2) ratio) <
        ENNReal.ofReal (2*Real.log 2/Real.log (20/9 : ℝ)-1) := by
  have sqrt_two_above_one : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have band_lower : Real.sqrt 3/4 < (7/16 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  filter_upwards [AE.irrational_ae_dimension_equality irrational_sqrt_two sqrt_two_above_one]
    with ratio dimension
  intro inside
  have equality := dimension ⟨band_lower.trans inside.1, inside.2.trans (by norm_num)⟩
  rw [equality]
  have lower_bound := expectedDimension_strictly_increasing (by norm_num : (0 : ℝ) < 7/16)
    inside.1 (inside.2.trans (by norm_num : (9/20 : ℝ) < 1))
  have upper_bound := expectedDimension_strictly_increasing
    ((by norm_num : (0 : ℝ) < 7/16).trans inside.1) inside.2 (by norm_num : (9/20 : ℝ) < 1)
  have lower_positive : 0 < expectedDimension (7/16 : ℝ) :=
    First.Roots.expectedDimension_positive (by norm_num) (by norm_num)
  have lower_cast := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg lower_positive.le).mpr lower_bound
  have upper_cast := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (lower_positive.trans lower_bound).le).mpr upper_bound
  constructor
  · simpa only [expectedDimension, show (1 : ℝ)/(7/16) = 16/7 by norm_num] using lower_cast
  · simpa only [expectedDimension, show (1 : ℝ)/(9/20) = 20/9 by norm_num] using upper_cast

end LambdaCantor.Manuscript

#print axioms LambdaCantor.Manuscript.introductory_last_transition
#print axioms LambdaCantor.Manuscript.introductory_ae_dimension
#print axioms LambdaCantor.Manuscript.average_sobolev
#print axioms LambdaCantor.Manuscript.ae_sqrt_two_dimension_bounds
