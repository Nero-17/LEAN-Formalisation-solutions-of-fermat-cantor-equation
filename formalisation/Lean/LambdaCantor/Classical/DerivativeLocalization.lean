import LambdaCantor.Classical.GeneralCover

noncomputable section
namespace LambdaCantor.Classical

theorem coordinateBounds_of_hasDerivAt (function horizontal vertical : ℝ → ℝ → ℝ)
    (horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (horizontal_derivative : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => function t y) (horizontal x y) x)
    (vertical_derivative : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => function x t) (vertical x y) y)
    (horizontal_bounds : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      horizontalLower ≤ horizontal x y ∧ horizontal x y ≤ horizontalUpper)
    (vertical_bounds : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      verticalLower ≤ vertical x y ∧ vertical x y ≤ verticalUpper) :
    CoordinateBounds function horizontalLower horizontalUpper verticalLower verticalUpper := by
  apply coordinateBounds_of_partial_derivatives
  · intro y hy x hx
    exact (horizontal_derivative x hx y hy).continuousAt.continuousWithinAt
  · intro x hx y hy
    exact (vertical_derivative x hx y hy).continuousAt.continuousWithinAt
  · intro y hy x hx
    exact (horizontal_derivative x ⟨hx.1.le, hx.2.le⟩ y hy).differentiableAt.differentiableWithinAt
  · intro x hx y hy
    exact (vertical_derivative x hx y ⟨hy.1.le, hy.2.le⟩).differentiableAt.differentiableWithinAt
  · intro y hy x hx
    rw [(horizontal_derivative x ⟨hx.1.le, hx.2.le⟩ y hy).deriv]
    exact horizontal_bounds x ⟨hx.1.le, hx.2.le⟩ y hy
  · intro x hx y hy
    rw [(vertical_derivative x hx y ⟨hy.1.le, hy.2.le⟩).deriv]
    exact vertical_bounds x hx y ⟨hy.1.le, hy.2.le⟩

/-- Strict derivative inequalities persist with uniform separated bounds on a ball. -/
theorem derivative_bounds_near_point (horizontal vertical : (ℝ × ℝ) → ℝ)
    (point : ℝ × ℝ) (horizontal_continuous : ContinuousAt horizontal point)
    (vertical_continuous : ContinuousAt vertical point)
    (vertical_positive : 0 < vertical point)
    (first_gap : vertical point < horizontal point)
    (middle_gap : horizontal point < 3 * vertical point) :
    ∃ horizontalLower horizontalUpper verticalLower verticalUpper radius : ℝ,
      0 < radius ∧ 0 < verticalLower ∧ verticalUpper ≤ horizontalLower ∧
      horizontalUpper ≤ 3 * verticalLower ∧
      ∀ other, dist other point < radius →
        horizontalLower ≤ horizontal other ∧ horizontal other ≤ horizontalUpper ∧
        verticalLower ≤ vertical other ∧ vertical other ≤ verticalUpper := by
  let margin : ℝ := min (vertical point / 2)
    (min ((horizontal point - vertical point) / 4) ((3 * vertical point - horizontal point) / 8))
  have margin_positive : 0 < margin := by
    dsimp [margin]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have horizontal_near : ∀ᶠ other in nhds point,
      horizontal other ∈ Set.Ioo (horizontal point - margin) (horizontal point + margin) :=
    horizontal_continuous.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have vertical_near : ∀ᶠ other in nhds point,
      vertical other ∈ Set.Ioo (vertical point - margin) (vertical point + margin) :=
    vertical_continuous.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp (horizontal_near.and vertical_near)
  refine ⟨horizontal point - margin, horizontal point + margin,
    vertical point - margin, vertical point + margin, radius, positive, ?_, ?_, ?_, ?_⟩
  · have bound : margin ≤ vertical point / 2 := min_le_left _ _
    linarith
  · have bound : margin ≤ (horizontal point - vertical point) / 4 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · have bound : margin ≤ (3 * vertical point - horizontal point) / 8 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  · intro other nearby
    have bounds := contained nearby
    exact ⟨bounds.1.1.le, bounds.1.2.le, bounds.2.1.le, bounds.2.2.le⟩

theorem coordinateBounds_rescaled (function horizontal vertical : ℝ → ℝ → ℝ)
    (u v side horizontalLower horizontalUpper verticalLower verticalUpper : ℝ)
    (side_nonnegative : 0 ≤ side)
    (horizontal_derivative : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => function t (v + side * y))
        (horizontal (u + side * x) (v + side * y)) (u + side * x))
    (vertical_derivative : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => function (u + side * x) t)
        (vertical (u + side * x) (v + side * y)) (v + side * y))
    (horizontal_bounds : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      horizontalLower ≤ horizontal (u + side * x) (v + side * y) ∧
        horizontal (u + side * x) (v + side * y) ≤ horizontalUpper)
    (vertical_bounds : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      verticalLower ≤ vertical (u + side * x) (v + side * y) ∧
        vertical (u + side * x) (v + side * y) ≤ verticalUpper) :
    CoordinateBounds (fun x y => function (u + side * x) (v + side * y))
      (side * horizontalLower) (side * horizontalUpper)
      (side * verticalLower) (side * verticalUpper) := by
  apply coordinateBounds_of_hasDerivAt _
    (fun x y => side * horizontal (u + side * x) (v + side * y))
    (fun x y => side * vertical (u + side * x) (v + side * y))
  · intro x hx y hy
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (horizontal_derivative x hx y hy).comp x (((hasDerivAt_id x).const_mul side).const_add u)
  · intro x hx y hy
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (vertical_derivative x hx y hy).comp y (((hasDerivAt_id y).const_mul side).const_add v)
  · intro x hx y hy
    exact ⟨mul_le_mul_of_nonneg_left (horizontal_bounds x hx y hy).1 side_nonnegative,
      mul_le_mul_of_nonneg_left (horizontal_bounds x hx y hy).2 side_nonnegative⟩
  · intro x hx y hy
    exact ⟨mul_le_mul_of_nonneg_left (vertical_bounds x hx y hy).1 side_nonnegative,
      mul_le_mul_of_nonneg_left (vertical_bounds x hx y hy).2 side_nonnegative⟩

end LambdaCantor.Classical
