import LambdaCantor.First.RationalTopology

noncomputable section
open Set Filter Topology
namespace LambdaCantor.First

/-- Punctured-limit mechanism: an error zero at irrational points and bounded
by a locally uniform constant divided by the reduced denominator tends to
zero at every real center, including rational centers. -/
theorem punctured_limit_of_denominator_bound
    (function : ℝ → ℝ) (value center constant neighborhood : ℝ)
    (hneighborhood : 0 < neighborhood)
    (hlower : ∀ x : ℝ, 2 ≤ x → value ≤ function x)
    (hirrational : ∀ x : ℝ, 2 ≤ x → (∀ q : ℚ, x ≠ (q : ℝ)) →
      function x = value)
    (hrational : ∀ q : ℚ, 2 ≤ (q : ℝ) →
      |(q : ℝ) - center| < neighborhood →
      function q - value ≤ constant / q.den) :
    Tendsto function (𝓝[{x : ℝ | 2 ≤ x ∧ x ≠ center}] center) (𝓝 value) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨denominatorBound, hbound⟩ := exists_nat_gt (constant / epsilon)
  obtain ⟨radius, hradius, hdenominator⟩ :=
    rational_denominators_escape center denominatorBound
  refine ⟨min radius neighborhood, lt_min hradius hneighborhood, ?_⟩
  intro x hx hnear
  rw [Real.dist_eq] at hnear ⊢
  rw [abs_of_nonneg (sub_nonneg.mpr (hlower x hx.1))]
  by_cases hrationalPoint : ∃ q : ℚ, x = (q : ℝ)
  · obtain ⟨q, rfl⟩ := hrationalPoint
    have hden := hdenominator q hx.2 (hnear.trans_le (min_le_left _ _))
    have hdenpos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hdenreal : (denominatorBound : ℝ) < q.den := by exact_mod_cast hden
    have hconstant : constant < epsilon * (q.den : ℝ) := by
      have := (div_lt_iff₀ hepsilon).mp (hbound.trans hdenreal)
      nlinarith
    exact (hrational q hx.1 (hnear.trans_le (min_le_right _ _))).trans_lt
      ((div_lt_iff₀ hdenpos).mpr (by nlinarith))
  · have hvalue := hirrational x hx.1 (by simpa using hrationalPoint)
    rw [hvalue, sub_self]
    exact hepsilon

end LambdaCantor.First
