import LambdaCantor.AE.DigitResidual

open Filter
open scoped Topology

namespace LambdaCantor.AE

/-- The local second derivative formula. Only a neighbourhood of the parameter
is required, so this applies to power series defined differentiably on (0,1).
It does not require a global differentiable extension of the series. -/
theorem hasDerivAt_deriv_digitResidual_local (depth : ℕ) (digit : ℝ)
    {function firstDerivative : ℝ → ℝ} {secondDerivative ratio : ℝ}
    (hfunction : ∀ᶠ parameter in 𝓝 ratio,
      HasDerivAt function (firstDerivative parameter) parameter)
    (hfirst : HasDerivAt firstDerivative secondDerivative ratio) :
    HasDerivAt
      (deriv (fun parameter => digit * firstDifferencePrefactor depth parameter * function parameter))
      (digit * (deriv (deriv (firstDifferencePrefactor depth)) ratio * function ratio +
        2 * deriv (firstDifferencePrefactor depth) ratio * firstDerivative ratio +
        firstDifferencePrefactor depth ratio * secondDerivative)) ratio := by
  have hprefactor := hasDerivAt_firstDifferencePrefactor depth ratio
  rw [← hprefactor.deriv] at hprefactor
  have hsecond := hasDerivAt_deriv_firstDifferencePrefactor depth ratio
  rw [← hsecond.deriv] at hsecond
  have hmodel : HasDerivAt
      (fun parameter => digit *
        (deriv (firstDifferencePrefactor depth) parameter * function parameter +
          firstDifferencePrefactor depth parameter * firstDerivative parameter))
      (digit * (deriv (deriv (firstDifferencePrefactor depth)) ratio * function ratio +
        2 * deriv (firstDifferencePrefactor depth) ratio * firstDerivative ratio +
        firstDifferencePrefactor depth ratio * secondDerivative)) ratio := by
    convert ((hsecond.mul hfunction.self_of_nhds).add
      (hprefactor.mul hfirst)).const_mul digit using 1 <;>
      first | rfl | (funext parameter; simp only [Pi.add_apply, Pi.mul_apply]) | ring
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [hfunction] with parameter hparameter
  exact (hasDerivAt_digitResidual depth digit hparameter).deriv

end LambdaCantor.AE
