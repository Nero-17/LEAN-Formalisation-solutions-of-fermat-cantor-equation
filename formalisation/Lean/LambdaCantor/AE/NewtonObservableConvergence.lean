import LambdaCantor.AE.NewtonMixture
import LambdaCantor.AE.KernelConvergence

noncomputable section
open Filter
open scoped Topology

namespace LambdaCantor.AE

/-- The quadratic same-address estimate identifies the pointwise limit of
the actual depth observables with the actual root, on the original source. -/
theorem newtonMixtureObservable_tendsto_root
    (kernels : ∀ depth : ℕ, (Fin depth → Bool × Bool) → FrozenNewtonKernel)
    (root : (ℕ → Bool × Bool) → ℝ) (shift : ℕ)
    {upper constant rho : ℝ} (upper_positive : 0 < upper) (upper_less_one : upper < 1)
    (quadratic_error : ∀ depth digits,
      |newtonMixtureObservable depth (kernels depth) digits-root digits| ≤
        constant*rho^2*(((shift+depth+1 : ℕ) : ℝ))*(upper^depth)^2) :
    ∀ digits : ℕ → Bool × Bool,
      Tendsto (fun depth => newtonMixtureObservable depth (kernels depth) digits) atTop (𝓝 (root digits)) := by
  have square_positive : 0 < upper^2 := pow_pos upper_positive 2
  have square_less_one : upper^2 < 1 := by nlinarith
  have limit := ((summable_shifted_polynomial_geometric shift 1 square_positive square_less_one).tendsto_atTop_zero).const_mul
    (constant*rho^2)
  have limit' : Tendsto (fun depth : ℕ =>
      constant*rho^2*(((shift+depth+1 : ℕ) : ℝ))*(upper^depth)^2) atTop (𝓝 0) := by
    convert limit using 1
    · funext depth
      rw [pow_one, show (upper^2)^depth = (upper^depth)^2 by
        rw [← pow_mul, Nat.mul_comm 2 depth, pow_mul]]
      ring
    · simp
  intro digits
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun depth => dist_nonneg) (fun depth => ?_) limit'
  simpa only [Real.dist_eq] using quadratic_error depth digits

end LambdaCantor.AE
