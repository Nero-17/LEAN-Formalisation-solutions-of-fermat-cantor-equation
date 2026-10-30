import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace LambdaCantor.Integer

/-- Polynomial quotient in the exact factorization of the Fermat residual. -/
noncomputable def fermatQuotient (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (1-z)^i

theorem fermat_factorization (n : ℕ) (z : ℝ) :
    1-(1-z)^n = z * fermatQuotient n z := by
  induction n with
  | zero => simp [fermatQuotient]
  | succ n ih =>
    simp only [fermatQuotient, Finset.sum_range_succ] at ih ⊢
    rw [pow_succ]
    nlinarith [ih]

theorem fermatQuotient_zero (n : ℕ) : fermatQuotient n 0 = n := by
  simp [fermatQuotient]

theorem continuous_fermatQuotient (n : ℕ) : Continuous (fermatQuotient n) := by
  unfold fermatQuotient
  exact continuous_finset_sum _ (fun i _ => (continuous_const.sub continuous_id).pow i)

/-- The rescaled residual has a continuous polynomial extension to scale zero. -/
theorem rescaled_fermat_residual (n : ℕ) (scale v : ℝ) (nonzero : scale ≠ 0) :
    (1-(1-scale*v)^n) / scale = v * fermatQuotient n (scale*v) := by
  rw [fermat_factorization]
  field_simp [nonzero]
  <;> ring

theorem rescaled_fermat_limit (n : ℕ) (v : ℝ) :
    Filter.Tendsto (fun scale : ℝ => v * fermatQuotient n (scale*v))
      (nhds 0) (nhds (v*n)) := by
  have hc : Continuous (fun scale : ℝ => v * fermatQuotient n (scale*v)) :=
    continuous_const.mul ((continuous_fermatQuotient n).comp
      (continuous_id.mul continuous_const))
  simpa only [zero_mul, fermatQuotient_zero] using hc.tendsto 0

/-- Zeroth-order logarithmic transfer. The polynomial is nonzero at zero
when n>0 and v>0, so continuity of log is applicable to the exact residual. -/
theorem logarithmic_fermat_limit (n : ℕ) (positive_n : 0 < n)
    (v : ℝ) (positive_v : 0 < v) :
    Filter.Tendsto (fun scale : ℝ => Real.log (v * fermatQuotient n (scale*v)))
      (nhds 0) (nhds (Real.log (v*n))) := by
  have nonzero : v * (n : ℝ) ≠ 0 := by positivity
  exact (Real.continuousAt_log nonzero).tendsto.comp (rescaled_fermat_limit n v)

/-- Exact derivative of the polynomial extension, including scale=0. -/
theorem hasDerivAt_rescaled_fermat (n : ℕ) (scale v : ℝ) :
    HasDerivAt (fun t => t * fermatQuotient n (scale*t))
      ((n : ℝ) * (1-scale*v)^(n-1)) v := by
  by_cases hzero : scale = 0
  · subst scale
    simpa only [zero_mul, fermatQuotient_zero, sub_zero, one_pow, mul_one, one_mul, id_eq]
      using (hasDerivAt_id v).mul_const (n : ℝ)
  · have hd := (((((hasDerivAt_id v).const_mul scale).const_sub 1).pow n).const_sub 1).div_const scale
    have heq : (fun t : ℝ => t * fermatQuotient n (scale*t)) =
        (fun t : ℝ => (1-(1-scale*t)^n)/scale) := by
      funext t
      exact (rescaled_fermat_residual n scale t hzero).symm
    rw [heq]
    convert! hd using 1 <;> simp only [Pi.pow_apply, id_eq, mul_one] <;>
      (try field_simp [hzero]) <;> ring

/-- Joint continuity is the ingredient for uniform derivative control on
the fixed compact source rectangle; this is stronger than convergence at
one chosen spatial point. -/
theorem continuous_rescaled_derivative (n : ℕ) :
    Continuous (fun parameter : ℝ × ℝ =>
      (n : ℝ) * (1-parameter.1*parameter.2)^(n-1)) :=
  continuous_const.mul ((continuous_const.sub (continuous_fst.mul continuous_snd)).pow _)

theorem continuous_rescaled_fermat (n : ℕ) :
    Continuous (fun parameter : ℝ × ℝ =>
      parameter.2 * fermatQuotient n (parameter.1*parameter.2)) :=
  continuous_snd.mul ((continuous_fermatQuotient n).comp
    (continuous_fst.mul continuous_snd))

end LambdaCantor.Integer

