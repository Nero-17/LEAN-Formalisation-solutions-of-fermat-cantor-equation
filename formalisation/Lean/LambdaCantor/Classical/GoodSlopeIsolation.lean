import LambdaCantor.Classical.DifferentiableIsolation
import LambdaCantor.Integer.GoodSlopeDomains

noncomputable section
namespace LambdaCantor.Classical

theorem good_slope_bounds (slope : ℝ) (good : Integer.GoodSlope slope) :
    1 < slope ∧ slope < 3 := by
  rcases good with band | band | band | band | band <;> constructor <;> linarith [band.1, band.2]

theorem good_slope_infDist_eventually_periodic
    (slope : ℝ) (good : Integer.GoodSlope slope)
    (digits : ℕ → Fin 4) (tails : ℕ → ℝ)
    (vanishing : ∀ error > 0, ∃ start, ∀ depth ≥ start,
      Metric.infDist (tails depth) (exclusiveInterval slope (digits depth)) < error)
    (recurrence : ∀ depth, tails (depth+1) = 3 * tails depth -
      (((digits depth).val / 2 : ℕ) : ℝ) * slope -
      (((digits depth).val % 2 : ℕ) : ℝ)) :
    ∃ start, ∀ depth ≥ start, digits (depth+4) = digits depth := by
  have slope_bounds := good_slope_bounds slope good
  apply Integer.good_slope_domains_eventually_periodic slope good digits tails
    (fun depth => Metric.infDist (tails depth) (exclusiveInterval slope (digits depth)))
    (fun _ => Metric.infDist_nonneg) vanishing recurrence
  · intro depth
    exact (exclusiveInterval_infDist_bounds slope (tails depth) slope_bounds.1
      slope_bounds.2 (digits depth)).1
  · intro depth
    exact (exclusiveInterval_infDist_bounds slope (tails depth) slope_bounds.1
      slope_bounds.2 (digits depth)).2

theorem good_slope_isolated_coordinates_rational (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (first second : ℕ → Bool) (horizontal vertical : ℝ) (vertical_positive : 0 < vertical)
    (good : Integer.GoodSlope (horizontal / vertical))
    (derivative : (ℝ × ℝ) →L[ℝ] ℝ)
    (differentiable : HasFDerivAt (fun point : ℝ × ℝ => function point.1 point.2) derivative
      (address (1 / 3) first, address (1 / 3) second))
    (derivative_formula : ∀ direction, derivative direction =
      horizontal * direction.1 + vertical * direction.2)
    (radius : ℝ) (radius_positive : 0 < radius)
    (isolated : ∀ point ∈ cantorLevel function
      (function (address (1 / 3) first) (address (1 / 3) second)),
      dist point (address (1 / 3) first, address (1 / 3) second) < radius →
        point = (address (1 / 3) first, address (1 / 3) second)) :
    (∃ rational : ℚ, (rational : ℝ) = address (1/3) first) ∧
      (∃ rational : ℚ, (rational : ℝ) = address (1/3) second) := by
  have slope_bounds := good_slope_bounds (horizontal / vertical) good
  have vanishing := differentiable_isolation_exclusive function continuous _ _ _ _ bounds
    first_gap middle_gap first second horizontal vertical vertical_positive
    slope_bounds.1 slope_bounds.2 derivative differentiable derivative_formula
    radius radius_positive isolated
  obtain ⟨start, periodic⟩ := good_slope_infDist_eventually_periodic
    (horizontal/vertical) good
    (fun depth => digitLabel (first depth) (second depth))
    (linearTail (horizontal/vertical) first second) vanishing
    (linearTail_recurrence (horizontal/vertical) first second)
  have coordinates : ∀ depth ≥ start,
      first (depth+4) = first depth ∧ second (depth+4) = second depth := by
    intro depth large
    exact digitLabel_injective (periodic depth large)
  constructor
  · exact rational_address_of_eventually_periodic first
      ⟨start, 4, by omega, fun depth large => (coordinates depth large).1⟩
  · exact rational_address_of_eventually_periodic second
      ⟨start, 4, by omega, fun depth large => (coordinates depth large).2⟩


end LambdaCantor.Classical

