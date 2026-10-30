import LambdaCantor.AE.FreezingAverage

noncomputable section
open Set MeasureTheory
namespace LambdaCantor.AE
open First.PrefixSlopes

/-- Real-valued indicator form of the actual prefix overlap, ready for the
Bochner energy integral estimate. -/
theorem root_prefix_indicator_overlap
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    (depth : ℕ) (centres : (Fin depth → Bool × Bool) → ℝ)
    {radius point bound : ℝ} (bound_nonnegative : 0 ≤ bound)
    (displacement : ∀ word digits, digits ∈ prefixCylinder word →
      root digits ∈ Icc (centres word-radius) (centres word+radius))
    (small_ball : First.Roots.rootLaw root (Icc (point-2*radius) (point+2*radius)) ≤ ENNReal.ofReal bound) :
    (∑ word : Fin depth → Bool × Bool,
      (Icc (centres word-radius) (centres word+radius)).indicator
        (fun _ => (1/4 : ℝ)^depth) point) ≤ bound := by
  classical
  have mass_bound := root_prefix_interval_overlap_of_smallBall root root_measurable depth centres
    displacement small_ball
  have real_bound := ENNReal.toReal_mono ENNReal.ofReal_ne_top mass_bound
  have count_bound :
      ((Finset.univ.filter (fun word => point ∈ Icc (centres word-radius) (centres word+radius))).card : ℝ)
        * (1/4 : ℝ)^depth ≤ bound := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal bound_nonnegative] using real_bound
  convert count_bound using 1
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]

end LambdaCantor.AE
