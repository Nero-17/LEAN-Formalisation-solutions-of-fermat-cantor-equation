import LambdaCantor.Integer.NearAxisLog
import LambdaCantor.Integer.NearAxisCylinders
import Mathlib.Analysis.SpecificLimits.Basic

namespace LambdaCantor.Integer

theorem nearAxisLog_zero_residual (n d p q : ℕ) (P Q scale first second : ℝ)
    (uPositive : 0 < (P+first)/3^p)
    (residualPositive : 0 < ((Q+1-second)/3^q)*
      fermatQuotient n (scale*((Q+1-second)/3^q)))
    (equation : nearAxisLog n d p q P Q scale first second = 0) :
    (3 : ℝ)^d*((P+first)/3^p)^n =
      ((Q+1-second)/3^q)*fermatQuotient n (scale*((Q+1-second)/3^q)) := by
  have leftPositive : 0 < (3 : ℝ)^d*((P+first)/3^p)^n := by positivity
  apply Real.log_injOn_pos leftPositive residualPositive
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
  unfold nearAxisLog at equation
  linarith

theorem near_axis_scale_tendsto (n d : ℕ) (positive : 0 < n) :
    Filter.Tendsto (fun k : ℕ => (1/3 : ℝ)^(n*k+d)) Filter.atTop (nhds 0) := by
  have powerPositive : (0 : ℝ) ≤ (1/3 : ℝ)^n := by positivity
  have powerSmall : (1/3 : ℝ)^n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have result := (tendsto_pow_atTop_nhds_zero_of_lt_one powerPositive powerSmall).mul_const
    ((1/3 : ℝ)^d)
  simpa only [pow_add,pow_mul,zero_mul] using result

theorem near_axis_log_zero_fermat (n d p q k : ℕ) (P Q first second : ℝ)
    (uPositive : 0 < (P+first)/3^p)
    (residualPositive : 0 < ((Q+1-second)/3^q)*
      fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-second)/3^q)))
    (equation : nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)) first second = 0) :
    ((1/3 : ℝ)^k*((P+first)/3^p))^n+
      (1-(1/3 : ℝ)^(n*k+d)*((Q+1-second)/3^q))^n = 1 := by
  have leftPositive : 0 < (3 : ℝ)^d*((P+first)/3^p)^n := by positivity
  have logarithms : Real.log ((3 : ℝ)^d*((P+first)/3^p)^n) =
      Real.log (((Q+1-second)/3^q)*
        fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-second)/3^q))) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow]
    unfold nearAxisLog at equation
    linarith
  have residual := Real.log_injOn_pos leftPositive residualPositive logarithms
  have factorization := fermat_factorization n ((1/3 : ℝ)^(n*k+d)*((Q+1-second)/3^q))
  have scaleCancellation : (1/3 : ℝ)^(n*k+d)*(3 : ℝ)^d = (1/3 : ℝ)^(n*k) := by
    rw [pow_add,one_div_pow,one_div_pow]
    field_simp
  have powerEquality : ((1/3 : ℝ)^k*((P+first)/3^p))^n =
      (1/3 : ℝ)^(n*k+d)*((3 : ℝ)^d*((P+first)/3^p)^n) := by
    rw [mul_pow,← pow_mul,← mul_assoc,scaleCancellation,Nat.mul_comm k n]
  rw [powerEquality,residual]
  nlinarith [factorization]

end LambdaCantor.Integer
