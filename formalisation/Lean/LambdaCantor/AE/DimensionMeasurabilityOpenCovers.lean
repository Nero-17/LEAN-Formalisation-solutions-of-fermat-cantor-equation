import LambdaCantor.AE.DimensionMeasurability

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace LambdaCantor.AE

/-- The certificate space can be uncountable: an arbitrary union of open
parameter-containment tests is still open. -/
structure FiniteOpenCoverCertificate (dimension : ℝ) (scale : ℝ≥0∞) where
  length : ℕ
  sets : Fin length → Set (ℝ × ℝ)
  isOpen_sets : ∀ index, IsOpen (sets index)
  diameter_bound : ∀ index, Metric.ediam (sets index) ≤ scale
  cost_bound : (∑ index, Metric.ediam (sets index) ^ dimension) ≤ scale

def FiniteOpenCoverTest (dimension : ℝ) (scale : ℕ → ℝ≥0∞)
    (fibre : Set (ℝ × ℝ)) : Prop :=
  ∀ precision : ℕ, ∃ certificate : FiniteOpenCoverCertificate dimension (scale precision),
    fibre ⊆ ⋃ index, certificate.sets index

theorem isOpen_exists_finiteOpenCover {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper)
    (dimension : ℝ) (scale : ℝ≥0∞) :
    IsOpen {ratio : Set.Icc lower upper |
      ∃ certificate : FiniteOpenCoverCertificate dimension scale,
        intersection exponent ratio.val ⊆ ⋃ index, certificate.sets index} := by
  simp only [setOf_exists]
  apply isOpen_iUnion
  intro certificate
  exact isOpen_intersection_subset exponent_positive lower_nonnegative upper_lt_one ordered
    (isOpen_iUnion certificate.isOpen_sets)

theorem measurableSet_finiteOpenCoverTest {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper)
    (dimension : ℝ) (scale : ℕ → ℝ≥0∞) :
    MeasurableSet {ratio : Set.Icc lower upper |
      FiniteOpenCoverTest dimension scale (intersection exponent ratio.val)} := by
  unfold FiniteOpenCoverTest
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro precision
  exact (isOpen_exists_finiteOpenCover exponent_positive lower_nonnegative upper_lt_one ordered
    dimension (scale precision)).measurableSet

theorem hausdorffMeasure_zero_of_finiteOpenCoverTest
    {dimension : ℝ} {scale : ℕ → ℝ≥0∞} {fibre : Set (ℝ × ℝ)}
    (scale_zero : Tendsto scale atTop (𝓝 0))
    (test : FiniteOpenCoverTest dimension scale fibre) :
    Measure.hausdorffMeasure dimension fibre = 0 := by
  classical
  choose certificate covered using test
  have measure_bound := Measure.hausdorffMeasure_le_liminf_sum dimension fibre scale scale_zero
    (fun precision => (certificate precision).sets)
    (Eventually.of_forall fun precision => (certificate precision).diameter_bound)
    (Eventually.of_forall covered)
  apply le_antisymm _ bot_le
  calc
    Measure.hausdorffMeasure dimension fibre ≤
        liminf (fun precision => ∑ index,
          Metric.ediam ((certificate precision).sets index) ^ dimension) atTop := measure_bound
    _ ≤ liminf scale atTop := liminf_le_liminf
      (Eventually.of_forall fun precision => (certificate precision).cost_bound)
    _ = 0 := scale_zero.liminf_eq

end LambdaCantor.AE
