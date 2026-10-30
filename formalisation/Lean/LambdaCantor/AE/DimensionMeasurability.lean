import LambdaCantor.ParameterContinuity

noncomputable section
open Set
namespace LambdaCantor.AE

/-- Closed graph plus compactness makes containment in any fixed open spatial set
an open condition on a compact parameter band. -/
theorem isOpen_intersection_subset {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper)
    {spatialOpen : Set (ℝ × ℝ)} (spatial_open : IsOpen spatialOpen) :
    IsOpen {ratio : Set.Icc lower upper | intersection exponent ratio.val ⊆ spatialOpen} := by
  have compact_bad :=
    (isCompact_parameter_intersection exponent_positive lower_nonnegative upper_lt_one ordered).inter_right
      (spatial_open.isClosed_compl.preimage continuous_snd)
  have closed_bad := (compact_bad.image continuous_fst).isClosed
  have open_good := (closed_bad.preimage
    (continuous_subtype_val : Continuous (fun ratio : Set.Icc lower upper => ratio.val))).isOpen_compl
  convert open_good using 1
  ext ratio
  constructor
  · intro contained bad
    obtain ⟨point, ⟨graph_mem, outside⟩, projection⟩ := bad
    exact outside (contained (by simpa [projection] using graph_mem.2))
  · intro no_bad point fibre_mem
    by_contra outside
    apply no_bad
    exact ⟨(ratio.val, point), ⟨⟨ratio.property, fibre_mem⟩, outside⟩, rfl⟩

/-- Every specified finite family of open balls gives a Borel cover test. -/
theorem isOpen_intersection_finite_ball_cover {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper)
    (length : ℕ) (centres : Fin length → ℝ × ℝ) (radii : Fin length → ℝ) :
    IsOpen {ratio : Set.Icc lower upper |
      intersection exponent ratio.val ⊆ ⋃ index, Metric.ball (centres index) (radii index)} :=
  isOpen_intersection_subset exponent_positive lower_nonnegative upper_lt_one ordered
    (isOpen_iUnion fun _ => Metric.isOpen_ball)

/-- Countable intersections and unions of finite-cover tests are measurable.
This is the descriptive-set part of the dimension argument, separated from the
still-required equivalence with the Hausdorff-measure definition. -/
theorem measurableSet_intersection_countable_cover_test {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper)
    (length : ℕ → ℕ → ℕ)
    (centres : (precision certificate : ℕ) → Fin (length precision certificate) → ℝ × ℝ)
    (radii : (precision certificate : ℕ) → Fin (length precision certificate) → ℝ)
    (admissible : ℕ → ℕ → Prop) :
    MeasurableSet {ratio : Set.Icc lower upper | ∀ precision : ℕ,
      ∃ certificate : ℕ, admissible precision certificate ∧
        intersection exponent ratio.val ⊆
          ⋃ index, Metric.ball (centres precision certificate index) (radii precision certificate index)} := by
  simp only [setOf_forall, setOf_exists, setOf_and]
  apply MeasurableSet.iInter
  intro precision
  apply MeasurableSet.iUnion
  intro certificate
  apply MeasurableSet.inter
  · by_cases valid : admissible precision certificate <;> simp [valid]
  · exact (isOpen_intersection_finite_ball_cover exponent_positive lower_nonnegative
      upper_lt_one ordered _ _ _).measurableSet

end LambdaCantor.AE
