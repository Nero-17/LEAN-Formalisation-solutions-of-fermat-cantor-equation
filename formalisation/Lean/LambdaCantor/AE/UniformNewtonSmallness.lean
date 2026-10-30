import LambdaCantor.AE.KernelConvergence

noncomputable section
open Filter
open scoped Topology

namespace LambdaCantor.AE

/-- A single large initial depth makes every normalized Newton error small,
uniformly over all subsequent prefix depths. -/
theorem uniform_newton_polynomial_geometric_smallness
    {center ratio constant epsilon : ℝ}
    (center_positive : 0 < center) (center_less_one : center < 1)
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1)
    (constant_nonnegative : 0 ≤ constant) (epsilon_positive : 0 < epsilon) :
    ∀ᶠ length : ℕ in atTop, ∀ depth : ℕ,
      constant*center^length*(((length+depth+1 : ℕ) : ℝ))*ratio^depth ≤ epsilon := by
  have limit := (total_kernel_error_tendsto_zero 1 ratio_positive ratio_less_one
    center_positive center_less_one).const_mul constant
  have limit' : Tendsto (fun length : ℕ => constant*(center^length*
      ∑' depth : ℕ, (((length+depth+1 : ℕ) : ℝ))*ratio^depth)) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero] using limit
  filter_upwards [limit'.eventually (gt_mem_nhds epsilon_positive)] with length small
  intro depth
  have term := (summable_shifted_polynomial_geometric length 1 ratio_positive ratio_less_one).le_tsum depth
    (fun other _ => by positivity)
  have bound := mul_le_mul_of_nonneg_left term
    (mul_nonneg constant_nonnegative (pow_nonneg center_positive.le length))
  calc
    constant*center^length*(((length+depth+1 : ℕ) : ℝ))*ratio^depth ≤
        constant*(center^length*
          ∑' depth : ℕ, (((length+depth+1 : ℕ) : ℝ))*ratio^depth) := by
      simpa only [pow_one, mul_assoc] using bound
    _ ≤ epsilon := small.le

end LambdaCantor.AE
