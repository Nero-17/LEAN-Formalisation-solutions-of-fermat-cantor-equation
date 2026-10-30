import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last

/-- Adding the maximal-curvature quadratic makes the logarithm convex on the
unit interval. Both derivatives and their sign are checked explicitly. -/
theorem convex_log_add_quadratic {relativeLength : ℝ} (nonnegative : 0 ≤ relativeLength) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun coordinate => Real.log (1+relativeLength*coordinate)+relativeLength^2/2*coordinate^2) := by
  have first_derivative : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt
        (fun value => Real.log (1+relativeLength*value)+relativeLength^2/2*value^2)
        (relativeLength/(1+relativeLength*coordinate)+relativeLength^2*coordinate) coordinate := by
    intro coordinate membership
    have argument_positive : 0 < 1+relativeLength*coordinate := by
      nlinarith [mul_nonneg nonnegative membership.1]
    have affine := ((hasDerivAt_id coordinate).const_mul relativeLength).const_add 1
    have logarithm := affine.log argument_positive.ne'
    have quadratic := ((hasDerivAt_id coordinate).pow 2).const_mul (relativeLength^2/2)
    convert! logarithm.add quadratic using 1 <;> (try dsimp) <;> ring
  have second_derivative : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt
        (fun value => relativeLength/(1+relativeLength*value)+relativeLength^2*value)
        (-(relativeLength^2)/(1+relativeLength*coordinate)^2+relativeLength^2) coordinate := by
    intro coordinate membership
    have argument_positive : 0 < 1+relativeLength*coordinate := by
      nlinarith [mul_nonneg nonnegative membership.1]
    have affine := ((hasDerivAt_id coordinate).const_mul relativeLength).const_add 1
    have quotient := (hasDerivAt_const coordinate relativeLength).div affine argument_positive.ne'
    have linear := (hasDerivAt_id coordinate).const_mul (relativeLength^2)
    convert! quotient.add linear using 1 <;> (try dsimp) <;> ring
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
    (fun coordinate membership => (first_derivative coordinate membership).continuousAt.continuousWithinAt)
    (fun coordinate membership =>
      (first_derivative coordinate (interior_subset membership)).hasDerivWithinAt)
    (fun coordinate membership =>
      (second_derivative coordinate (interior_subset membership)).hasDerivWithinAt)
  intro coordinate membership
  have coordinate_nonnegative := (interior_subset membership : coordinate ∈ Set.Icc (0 : ℝ) 1).1
  have argument_lower : 1 ≤ 1+relativeLength*coordinate := by
    nlinarith [mul_nonneg nonnegative coordinate_nonnegative]
  have argument_positive : 0 < 1+relativeLength*coordinate := by linarith
  have denominator_positive : 0 < (1+relativeLength*coordinate)^2 := sq_pos_of_pos argument_positive
  have fraction_bound : relativeLength^2/(1+relativeLength*coordinate)^2 ≤ relativeLength^2 := by
    apply (div_le_iff₀ denominator_positive).mpr
    nlinarith [mul_nonneg (sq_nonneg relativeLength)
      (show 0 ≤ (1+relativeLength*coordinate)^2-1 by nlinarith)]
  rw [neg_div]
  linarith

/-- Actual one-sided logarithmic secant error, with the sharp elementary
uniform bound obtained from s(1-s) ≤ 1/4. -/
theorem log_secant_error_bounds {relativeLength coordinate : ℝ}
    (nonnegative : 0 ≤ relativeLength) (coordinate_mem : coordinate ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ Real.log (1+relativeLength*coordinate)-coordinate*Real.log (1+relativeLength) ∧
      Real.log (1+relativeLength*coordinate)-coordinate*Real.log (1+relativeLength) ≤ relativeLength^2/8 := by
  have weight_nonnegative : 0 ≤ 1-coordinate := by linarith [coordinate_mem.2]
  have weights : (1-coordinate)+coordinate = 1 := by ring
  have lower := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1+relativeLength ∈ Set.Ioi (0 : ℝ) by change 0 < 1+relativeLength; linarith)
    weight_nonnegative coordinate_mem.1 weights
  have convexity := convex_log_add_quadratic nonnegative
  have upper := convexity.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    weight_nonnegative coordinate_mem.1 weights
  have lower_argument : (1-coordinate)*1+coordinate*(1+relativeLength) =
      1+relativeLength*coordinate := by ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at lower
  rw [lower_argument] at lower
  simp [smul_eq_mul] at upper
  constructor
  · linarith
  · nlinarith [mul_nonneg (sq_nonneg relativeLength) (sq_nonneg (coordinate-1/2))]

theorem scaled_log_secant_error_bounds {exponent relativeLength coordinate : ℝ}
    (exponent_nonnegative : 0 ≤ exponent) (nonnegative : 0 ≤ relativeLength)
    (coordinate_mem : coordinate ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ exponent*(Real.log (1+relativeLength*coordinate)-coordinate*Real.log (1+relativeLength)) ∧
      exponent*(Real.log (1+relativeLength*coordinate)-coordinate*Real.log (1+relativeLength)) ≤
        exponent*relativeLength^2/8 := by
  have bounds := log_secant_error_bounds nonnegative coordinate_mem
  constructor
  · exact mul_nonneg exponent_nonnegative bounds.1
  · nlinarith [mul_le_mul_of_nonneg_left bounds.2 exponent_nonnegative]

/-- This is the actual logarithmic cylinder map appearing in the large
exponent endpoint construction. -/
def largeLogarithmicCopy (exponent ratio : ℝ) (depth : ℕ) (coordinate : ℝ) : ℝ :=
  exponent*Real.log (1-ratio+ratio^depth*coordinate)

theorem large_logarithmic_copy_secant_bounds {exponent ratio coordinate : ℝ} (depth : ℕ)
    (exponent_nonnegative : 0 ≤ exponent) (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1)
    (coordinate_mem : coordinate ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ largeLogarithmicCopy exponent ratio depth coordinate-
        (exponent*Real.log (1-ratio)+
          exponent*Real.log (1+ratio^depth/(1-ratio))*coordinate) ∧
      largeLogarithmicCopy exponent ratio depth coordinate-
        (exponent*Real.log (1-ratio)+
          exponent*Real.log (1+ratio^depth/(1-ratio))*coordinate) ≤
        exponent*(ratio^depth/(1-ratio))^2/8 := by
  have complement_positive : 0 < 1-ratio := by linarith
  have relative_nonnegative : 0 ≤ ratio^depth/(1-ratio) :=
    div_nonneg (pow_nonneg ratio_positive.le _) complement_positive.le
  have argument_positive : 0 < 1+(ratio^depth/(1-ratio))*coordinate := by
    nlinarith [mul_nonneg relative_nonnegative coordinate_mem.1]
  have factor : (1-ratio)*(1+(ratio^depth/(1-ratio))*coordinate) =
      1-ratio+ratio^depth*coordinate := by
    field_simp [complement_positive.ne']
    <;> ring
  have logarithm : Real.log (1-ratio+ratio^depth*coordinate) =
      Real.log (1-ratio)+Real.log (1+(ratio^depth/(1-ratio))*coordinate) := by
    rw [← factor, Real.log_mul complement_positive.ne' argument_positive.ne']
  have bounds := scaled_log_secant_error_bounds exponent_nonnegative relative_nonnegative coordinate_mem
  unfold largeLogarithmicCopy
  rw [logarithm]
  constructor <;> nlinarith [bounds.1, bounds.2]

end LambdaCantor.Last
