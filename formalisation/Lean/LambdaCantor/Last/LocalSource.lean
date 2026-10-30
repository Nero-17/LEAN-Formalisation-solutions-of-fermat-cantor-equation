import LambdaCantor.Last.StrictReturnCriterion
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear

noncomputable section
open scoped NNReal Topology
namespace LambdaCantor.Last

theorem wordMap_antilipschitz {ratio : ℝ} (hpositive : 0 < ratio)
    (word : List (Bool × Bool)) :
    AntilipschitzWith ((⟨ratio ^ word.length, pow_nonneg hpositive.le _⟩ : ℝ≥0)⁻¹)
      (wordMap ratio word) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  rw [wordMap_distance, abs_of_pos hpositive]
  change dist first second ≤ (ratio ^ word.length)⁻¹ *
    (ratio ^ word.length * dist first second)
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (pow_pos hpositive _)), one_mul]

theorem positive_dimension_of_cylinder_fibre {ratio : ℝ} (hpositive : 0 < ratio)
    (hless : ratio < 1) (word : List (Bool × Bool)) (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (hsource : 0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧
      function (wordMap ratio word point) = level}) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point = level} := by
  apply hsource.trans_le ((wordMap_antilipschitz hpositive word).le_dimH_image _ |>.trans (dimH_mono ?_))
  rintro point ⟨tail, htail, rfl⟩
  exact ⟨wordMap_mem_dust hpositive.le hless word htail.1, htail.2⟩

/-- Strict differentiability makes the linearization error uniformly Lipschitz-small
on every sufficiently deep Cantor cylinder through the base point. -/
theorem strict_derivative_cylinder_error {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    {function : (ℝ × ℝ) → ℝ} {linear : (ℝ × ℝ) →L[ℝ] ℝ} {point : ℝ × ℝ}
    (hderivative : HasStrictFDerivAt function linear point)
    (bound : ℝ≥0) (hbound : 0 < bound) :
    ∃ minimumDepth : ℕ, ∀ word : List (Bool × Bool), minimumDepth ≤ word.length →
      point ∈ wordCylinder ratio word →
      LipschitzOnWith bound (fun value => function value - linear value) (wordCylinder ratio word) := by
  have herror := hderivative.sub linear.hasStrictFDerivAt
  rw [sub_self] at herror
  obtain ⟨neighborhood, hneighborhood, hlipschitz⟩ :=
    herror.exists_lipschitzOnWith_of_nnnorm_lt bound (by simpa using hbound)
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hneighborhood
  obtain ⟨minimumDepth, hminimumDepth⟩ :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless).eventually
      (gt_mem_nhds hradius)).exists
  refine ⟨minimumDepth, ?_⟩
  intro word hdepth hpoint
  apply hlipschitz.mono
  intro value hvalue
  apply hball
  apply Metric.mem_ball.mpr
  exact ((wordCylinder_dist_le hpositive.le hless word hvalue hpoint).trans
    (pow_le_pow_of_le_one hpositive.le hless.le hdepth)).trans_lt hminimumDepth

/-- Transfer the robust linear return criterion to an actual nonlinear cylinder.
Only its linearization error and normalized level have to be checked. -/
theorem local_source_criterion (ratio : ℝ) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (linear : (ℝ × ℝ) →L[ℝ] ℝ) (levels : Set ℝ)
    (hcompact : IsCompact levels) (hnonempty : levels.Nonempty)
    (hreturns : ∀ level ∈ levels, ∃ pair : ReturnPair,
      linearWordReturn ratio linear.toLinearMap (pair.word false) level ∈ interior levels ∧
      linearWordReturn ratio linear.toLinearMap (pair.word true) level ∈ interior levels) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∃ neighborhood : Set ℝ,
      IsOpen neighborhood ∧ levels ⊆ neighborhood ∧
      ∀ bound : ℝ≥0, (bound : ℝ) < threshold →
      ∀ function : (ℝ × ℝ) → ℝ, ∀ level : ℝ, ∀ word : List (Bool × Bool),
      LipschitzOnWith bound (fun value => function value - linear value) (wordCylinder ratio word) →
      (level - function (wordMap ratio word 0)) / ratio ^ word.length ∈ neighborhood →
      0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point = level} := by
  obtain ⟨threshold, hthreshold, neighborhood, hopen, hsubset, hcriterion⟩ :=
    strict_return_criterion ratio hpositive hhalf linear levels hcompact hnonempty hreturns
  refine ⟨threshold, hthreshold, neighborhood, hopen, hsubset, ?_⟩
  intro bound hbound function level word hlipschitz hlevel
  obtain ⟨extension, hextension, hagreement⟩ := hlipschitz.extend_real
  have hsource := hcriterion bound hbound
    (normalizedError extension (ratio ^ word.length) (wordMap ratio word 0))
    (normalizedError_lipschitz hextension _ (pow_pos hpositive _) _).lipschitzOnWith
    (normalizedError_zero _ _ _)
    ((level - function (wordMap ratio word 0)) / ratio ^ word.length) hlevel
  apply positive_dimension_of_cylinder_fibre hpositive (by linarith) word function level
  apply hsource.trans_le (dimH_mono ?_)
  intro point hpoint
  refine ⟨hpoint.1, ?_⟩
  have himage : wordMap ratio word point ∈ wordCylinder ratio word := ⟨point, hpoint.1, rfl⟩
  have hcorner : wordMap ratio word 0 ∈ wordCylinder ratio word :=
    ⟨0, ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩, rfl⟩
  have hfunction_image : linear (wordMap ratio word point) + extension (wordMap ratio word point) =
      function (wordMap ratio word point) := by rw [← hagreement himage]; ring
  have hfunction_corner : linear (wordMap ratio word 0) + extension (wordMap ratio word 0) =
      function (wordMap ratio word 0) := by rw [← hagreement hcorner]; ring
  have identity := restriction_identity linear.toLinearMap extension (ratio ^ word.length) level
    (ne_of_gt (pow_pos hpositive _)) (wordMap ratio word 0) point
  simp only [restrictPoint, ← wordMap_affine, returnLevel] at identity
  change linear (wordMap ratio word point) + extension (wordMap ratio word point) - level =
    ratio ^ word.length * (linear point +
      normalizedError extension (ratio ^ word.length) (wordMap ratio word 0) point -
      (level - (linear (wordMap ratio word 0) + extension (wordMap ratio word 0))) /
        ratio ^ word.length) at identity
  rw [hfunction_image, hfunction_corner, hpoint.2, sub_self, mul_zero] at identity
  exact sub_eq_zero.mp identity

end LambdaCantor.Last
