import LambdaCantor.Classical.GeneralFixedIsolation
import LambdaCantor.Classical.DifferentiableSquareApproximation
import LambdaCantor.Classical.NoIsolation

noncomputable section
namespace LambdaCantor.Classical

theorem infDist_interval_le_of_bounds (lower upper value error : ℝ)
    (ordered : lower ≤ upper) (nonnegative : 0 ≤ error)
    (bounds : lower-error ≤ value ∧ value ≤ upper+error) :
    Metric.infDist value (Set.Icc lower upper) ≤ error := by
  rcases le_total value lower with small | greater
  · apply le_trans (Metric.infDist_le_dist_of_mem (show lower ∈ Set.Icc lower upper from ⟨le_rfl, ordered⟩))
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr small)]
    linarith [bounds.1]
  · rcases le_total upper value with large | smaller
    · apply le_trans (Metric.infDist_le_dist_of_mem (show upper ∈ Set.Icc lower upper from ⟨ordered, le_rfl⟩))
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr large)]
      linarith [bounds.2]
    · apply le_trans (Metric.infDist_le_dist_of_mem (show value ∈ Set.Icc lower upper from ⟨greater, smaller⟩))
      simpa using nonnegative

/-- Genuine differentiability and the cover criterion imply vanishing distance to
the exclusive intervals at an isolated Cantor level point. -/
theorem differentiable_isolation_exclusive (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (first second : ℕ → Bool) (horizontal vertical : ℝ) (vertical_positive : 0 < vertical)
    (slope_lower : 1 < horizontal / vertical) (slope_upper : horizontal / vertical < 3)
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
    ∀ error > 0, ∃ start, ∀ depth ≥ start,
      Metric.infDist (linearTail (horizontal / vertical) first second depth)
        (exclusiveInterval (horizontal / vertical) (digitLabel (first depth) (second depth))) < error := by
  intro error positive
  let trimmed : ℝ := min (error/2) (min (1/6) ((horizontal/vertical-1)/6))
  have trimmed_positive : 0 < trimmed := by
    dsimp [trimmed]
    exact lt_min (by linarith) (lt_min (by norm_num) (by linarith))
  have trimmed_error : trimmed < error := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have trimmed_small : trimmed < 1/3 := by
    have bound : trimmed ≤ 1/6 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have trimmed_gap : trimmed < (horizontal/vertical-1)/3 := by
    have bound : trimmed ≤ (horizontal/vertical-1)/6 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  obtain ⟨analyticRadius, analytic_positive, approximation⟩ := differentiable_square_approximation
    function continuous _ _ _ _ bounds first_gap middle_gap
    (address (1/3) first) (address (1/3) second) horizontal vertical vertical_positive
    derivative differentiable derivative_formula trimmed trimmed_positive
  have geometric : Filter.Tendsto (fun depth : ℕ => (1/3 : ℝ)^depth) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  obtain ⟨approximationStart, side_small⟩ := Filter.eventually_atTop.mp
    ((tendsto_order.mp geometric).2 analyticRadius analytic_positive)
  obtain ⟨start, exclusive⟩ := general_isolated_level_fixed_error function first second
    (horizontal/vertical) slope_lower trimmed trimmed_small trimmed_gap approximationStart
    (fun depth large => approximation _ _ _ _ _ (tailAddress_bounds first depth)
      (tailAddress_bounds second depth) (by positivity) (side_small depth large))
    radius radius_positive isolated
  refine ⟨start, fun depth large => ?_⟩
  apply lt_of_le_of_lt _ trimmed_error
  have interval_nonempty := exclusiveInterval_nonempty (horizontal/vertical)
    slope_lower slope_upper (digitLabel (first depth) (second depth))
  have ordered := Set.nonempty_Icc.mp interval_nonempty
  change Metric.infDist _ (Set.Icc _ _) ≤ trimmed
  apply infDist_interval_le_of_bounds _ _ _ _ ordered trimmed_positive.le
  rw [← exclusiveLower_coefficient, ← exclusiveUpper_coefficient]
  exact exclusive depth large

theorem differentiable_isolated_coordinates_rational (function : ℝ → ℝ → ℝ)
    (continuous : ContinuousOn (fun point : ℝ × ℝ => function point.1 point.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (bounds : CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper)
    (first_gap : verticalUpper ≤ horizontalLower)
    (middle_gap : horizontalUpper ≤ 3 * verticalLower)
    (first second : ℕ → Bool) (horizontal vertical : ℝ) (vertical_positive : 0 < vertical)
    (slope_lower : 11/9 < horizontal / vertical) (slope_upper : horizontal / vertical < 2027/1624)
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
  have vanishing := differentiable_isolation_exclusive function continuous _ _ _ _ bounds
    first_gap middle_gap first second horizontal vertical vertical_positive
    (by linarith) (by linarith) derivative differentiable derivative_formula
    radius radius_positive isolated
  obtain ⟨start, periodic⟩ := infDist_exclusive_domains_eventually_periodic
    (horizontal/vertical) slope_lower slope_upper
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
