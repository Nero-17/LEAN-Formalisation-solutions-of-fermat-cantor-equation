import LambdaCantor.Integer.FermatPolynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Compactness.Compact

namespace LambdaCantor.Integer

noncomputable def fermatLogDerivative (n : ℕ) (scale value : ℝ) : ℝ :=
  (n : ℝ)*(1-scale*value)^(n-1)/(value*fermatQuotient n (scale*value))

theorem fermatLogDerivative_zero (n : ℕ) (positive : 0 < n) (value : ℝ)
    (nonzero : value ≠ 0) : fermatLogDerivative n 0 value = 1/value := by
  have nNonzero : (n : ℝ) ≠ 0 := by positivity
  unfold fermatLogDerivative
  simp only [zero_mul,sub_zero,one_pow,mul_one,fermatQuotient_zero]
  field_simp [nNonzero,nonzero]

theorem continuousAt_fermatLogDerivative (n : ℕ) (positive : 0 < n) (value : ℝ)
    (valuePositive : 0 < value) :
    ContinuousAt (fun parameter : ℝ × ℝ => fermatLogDerivative n parameter.1 parameter.2)
      (0,value) := by
  apply (continuous_rescaled_derivative n).continuousAt.div
    (continuous_rescaled_fermat n).continuousAt
  simp only [zero_mul,fermatQuotient_zero]
  positivity

/-- Uniform C1 control is derived from the explicit polynomial factorization,
on any fixed compact positive interval. No limiting-source oracle is assumed. -/
theorem near_axis_uniform_C1 (n : ℕ) (positive : 0 < n)
    (lower upper error : ℝ) (lowerPositive : 0 < lower) (errorPositive : 0 < error) :
    ∀ᶠ scale : ℝ in nhds 0, ∀ value ∈ Set.Icc lower upper,
      0 < value*fermatQuotient n (scale*value) ∧
      |Real.log (value*fermatQuotient n (scale*value))-Real.log (value*(n : ℝ))| < error ∧
      |fermatLogDerivative n scale value-1/value| < error := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro value membership
  have valuePositive : 0 < value := lowerPositive.trans_le membership.1
  have residualPositive : 0 < value*(n : ℝ) := by positivity
  have residualContinuous := (continuous_rescaled_fermat n).continuousAt (x := (0,value))
  have residualAtZero : value*fermatQuotient n (0*value) = value*(n : ℝ) := by
    rw [zero_mul,fermatQuotient_zero]
  have positiveNear : ∀ᶠ parameter : ℝ × ℝ in nhds (0,value),
      0 < parameter.2*fermatQuotient n (parameter.1*parameter.2) := by
    apply residualContinuous.eventually
    exact Ioi_mem_nhds (by simpa only [zero_mul, fermatQuotient_zero] using residualPositive)
  have logContinuous : ContinuousAt (fun parameter : ℝ × ℝ =>
      Real.log (parameter.2*fermatQuotient n (parameter.1*parameter.2))-
        Real.log (parameter.2*(n : ℝ))) (0,value) :=
    (residualContinuous.log (by simpa only [zero_mul, fermatQuotient_zero] using ne_of_gt residualPositive)).sub
      ((continuous_snd.mul continuous_const).continuousAt.log (ne_of_gt residualPositive))
  have derivativeContinuous : ContinuousAt (fun parameter : ℝ × ℝ =>
      fermatLogDerivative n parameter.1 parameter.2-1/parameter.2) (0,value) :=
    (continuousAt_fermatLogDerivative n positive value valuePositive).sub
      (continuousAt_const.div continuous_snd.continuousAt (ne_of_gt valuePositive))
  have logNear : ∀ᶠ parameter : ℝ × ℝ in nhds (0,value),
      Real.log (parameter.2*fermatQuotient n (parameter.1*parameter.2))-
        Real.log (parameter.2*(n : ℝ)) ∈ Set.Ioo (-error) error := by
    apply logContinuous.eventually
    simp only [zero_mul,fermatQuotient_zero,sub_self]
    exact Ioo_mem_nhds (by linarith) errorPositive
  have derivativeNear : ∀ᶠ parameter : ℝ × ℝ in nhds (0,value),
      fermatLogDerivative n parameter.1 parameter.2-1/parameter.2 ∈ Set.Ioo (-error) error := by
    apply derivativeContinuous.eventually
    dsimp only
    rw [fermatLogDerivative_zero n positive value (ne_of_gt valuePositive),sub_self]
    exact Ioo_mem_nhds (by linarith) errorPositive
  filter_upwards [positiveNear,logNear,derivativeNear] with parameter hp hl hd
  exact ⟨hp,abs_lt.mpr hl,abs_lt.mpr hd⟩

theorem hasDerivAt_logarithmic_residual (n : ℕ) (scale value : ℝ)
    (positive : 0 < value*fermatQuotient n (scale*value)) :
    HasDerivAt (fun t => Real.log (t*fermatQuotient n (scale*t)))
      (fermatLogDerivative n scale value) value := by
  exact (hasDerivAt_rescaled_fermat n scale value).log (ne_of_gt positive)

end LambdaCantor.Integer
