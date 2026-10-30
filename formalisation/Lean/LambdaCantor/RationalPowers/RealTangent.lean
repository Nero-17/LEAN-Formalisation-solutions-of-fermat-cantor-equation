import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.RationalPowers

def realFermatTangent (exponent : ℝ) (point : ℝ × ℝ) : ℝ :=
  point.2^(exponent-1)/point.1^(exponent-1)

theorem real_fermat_tangent_strict_of_first_lt (exponent : ℝ) (exponent_gt_one : 1 < exponent)
    (first second : ℝ × ℝ) (first_x : 0 < first.1) (first_y : 0 < first.2)
    (second_x : 0 < second.1) (second_y : 0 < second.2)
    (first_equation : first.1^exponent+first.2^exponent=1)
    (second_equation : second.1^exponent+second.2^exponent=1)
    (first_lt : first.1 < second.1) :
    realFermatTangent exponent second < realFermatTangent exponent first := by
  have exponent_positive : 0 < exponent := by linarith
  have predecessor_positive : 0 < exponent-1 := by linarith
  have first_powers : first.1^exponent < second.1^exponent :=
    Real.rpow_lt_rpow first_x.le first_lt exponent_positive
  have second_powers : second.2^exponent < first.2^exponent := by linarith
  have second_lt : second.2 < first.2 :=
    (Real.rpow_lt_rpow_iff second_y.le first_y.le exponent_positive).mp second_powers
  unfold realFermatTangent
  apply (div_lt_div_iff₀ (Real.rpow_pos_of_pos second_x _) (Real.rpow_pos_of_pos first_x _)).mpr
  calc
    second.2^(exponent-1)*first.1^(exponent-1) <
        first.2^(exponent-1)*first.1^(exponent-1) :=
      mul_lt_mul_of_pos_right (Real.rpow_lt_rpow second_y.le second_lt predecessor_positive)
        (Real.rpow_pos_of_pos first_x _)
    _ ≤ first.2^(exponent-1)*second.1^(exponent-1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_lt_rpow first_x.le first_lt predecessor_positive).le
          (Real.rpow_pos_of_pos first_y _).le

/-- The actual positive real Fermat arc has an injective tangent ratio for
every real exponent > 1, independently of arithmetic or certificates. -/
theorem real_fermat_tangent_injective (exponent : ℝ) (exponent_gt_one : 1 < exponent)
    (source : Set (ℝ × ℝ))
    (positive : ∀ point ∈ source, 0 < point.1 ∧ 0 < point.2)
    (equation : ∀ point ∈ source, point.1^exponent+point.2^exponent=1) :
    Set.InjOn (realFermatTangent exponent) source := by
  intro first first_mem second second_mem equality
  obtain ⟨first_x,first_y⟩ := positive first first_mem
  obtain ⟨second_x,second_y⟩ := positive second second_mem
  have first_equal : first.1 = second.1 := by
    rcases lt_trichotomy first.1 second.1 with less | equal | greater
    · have strict := real_fermat_tangent_strict_of_first_lt exponent exponent_gt_one first second
        first_x first_y second_x second_y (equation first first_mem) (equation second second_mem) less
      rw [equality] at strict
      exact False.elim (lt_irrefl _ strict)
    · exact equal
    · have strict := real_fermat_tangent_strict_of_first_lt exponent exponent_gt_one second first
        second_x second_y first_x first_y (equation second second_mem) (equation first first_mem) greater
      rw [equality] at strict
      exact False.elim (lt_irrefl _ strict)
  apply Prod.ext first_equal
  apply (Real.rpow_left_inj first_y.le second_y.le (by linarith : exponent ≠ 0)).mp
  have first_equation := equation first first_mem
  have second_equation := equation second second_mem
  rw [first_equal] at first_equation
  linarith

end LambdaCantor.RationalPowers

