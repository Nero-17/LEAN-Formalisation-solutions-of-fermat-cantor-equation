import LambdaCantor.Last.AnalyticIsolatedPerfect
import LambdaCantor.Common

noncomputable section
namespace LambdaCantor.Last

def fermatTangentRatio (exponent : ℝ) (point : ℝ × ℝ) : ℝ :=
  point.2 ^ (exponent-1) / point.1 ^ (exponent-1)

theorem fermatTangentRatio_strict_of_first_lt {exponent : ℝ}
    (exponent_gt_one : 1 < exponent) {first second : ℝ × ℝ}
    (first_positive : 0 < first.1 ∧ 0 < first.2)
    (second_positive : 0 < second.1 ∧ 0 < second.2)
    (first_level : first.1 ^ exponent + first.2 ^ exponent = 1)
    (second_level : second.1 ^ exponent + second.2 ^ exponent = 1)
    (first_lt : first.1 < second.1) :
    fermatTangentRatio exponent second < fermatTangentRatio exponent first := by
  have exponent_positive : 0 < exponent := by linarith
  have reduced_positive : 0 < exponent-1 := by linarith
  have first_power_lt := Real.rpow_lt_rpow first_positive.1.le first_lt exponent_positive
  have second_power_lt : second.2 ^ exponent < first.2 ^ exponent := by linarith
  have second_lt := (Real.rpow_lt_rpow_iff second_positive.2.le first_positive.2.le
    exponent_positive).mp second_power_lt
  apply (div_lt_div_iff₀ (Real.rpow_pos_of_pos second_positive.1 _)
    (Real.rpow_pos_of_pos first_positive.1 _)).2
  calc
    second.2 ^ (exponent-1) * first.1 ^ (exponent-1) <
        first.2 ^ (exponent-1) * first.1 ^ (exponent-1) :=
      mul_lt_mul_of_pos_right
        (Real.rpow_lt_rpow second_positive.2.le second_lt reduced_positive)
        (Real.rpow_pos_of_pos first_positive.1 _)
    _ ≤ first.2 ^ (exponent-1) * second.1 ^ (exponent-1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_lt_rpow first_positive.1.le first_lt reduced_positive).le
        (Real.rpow_pos_of_pos first_positive.2 _).le

theorem fermatTangentRatio_injective {exponent : ℝ} (exponent_gt_one : 1 < exponent)
    {source : Set (ℝ × ℝ)}
    (positive : ∀ point ∈ source, 0 < point.1 ∧ 0 < point.2)
    (on_level : ∀ point ∈ source, point.1 ^ exponent + point.2 ^ exponent = 1) :
    Set.InjOn (fermatTangentRatio exponent) source := by
  intro first first_mem second second_mem equal
  have first_equal : first.1 = second.1 := by
    rcases lt_trichotomy first.1 second.1 with less | same | greater
    · have strict := fermatTangentRatio_strict_of_first_lt exponent_gt_one
        (positive first first_mem) (positive second second_mem)
        (on_level first first_mem) (on_level second second_mem) less
      rw [equal] at strict
      exact (lt_irrefl _ strict).elim
    · exact same
    · have strict := fermatTangentRatio_strict_of_first_lt exponent_gt_one
        (positive second second_mem) (positive first first_mem)
        (on_level second second_mem) (on_level first first_mem) greater
      rw [equal] at strict
      exact (lt_irrefl _ strict).elim
  apply Prod.ext first_equal
  apply (Real.rpow_left_inj (positive first first_mem).2.le
    (positive second second_mem).2.le (by linarith : exponent ≠ 0)).mp
  have first_equation := on_level first first_mem
  have second_equation := on_level second second_mem
  rw [first_equal] at first_equation
  linarith

end LambdaCantor.Last
