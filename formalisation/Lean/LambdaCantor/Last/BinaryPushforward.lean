import LambdaCantor.Last.BinaryMeasure
import Mathlib.Topology.EMetricSpace.Diam

noncomputable section
open MeasureTheory Metric
open scoped ENNReal
namespace LambdaCantor.Last

/-- If different depth-d prefixes have separated images, a smaller-diameter set
has at most the mass of one prefix cylinder. -/
theorem binary_pushforward_small_set_bound
    {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    (coding : (ℕ → Bool) → X) (hmeasurable : Measurable coding)
    (depth : ℕ) (separation : ℝ≥0∞)
    (hseparation : ∀ first second : ℕ → Bool,
      (∃ position < depth, first position ≠ second position) →
      separation ≤ edist (coding first) (coding second))
    {subset : Set X} (hsubset : MeasurableSet subset)
    (hdiameter : ediam subset < separation) :
    binaryBranchMeasure.map coding subset ≤ (2 : ℝ≥0∞)⁻¹ ^ depth := by
  rw [Measure.map_apply hmeasurable hsubset]
  by_cases hnonempty : (coding ⁻¹' subset).Nonempty
  · obtain ⟨first, hfirst⟩ := hnonempty
    have hcontained : coding ⁻¹' subset ⊆ branchCylinder depth first := by
      intro second hsecond position hposition
      by_contra hne
      have hdist := hseparation second first ⟨position, hposition, hne⟩
      have hdiam := edist_le_ediam_of_mem
        (show coding second ∈ subset from hsecond)
        (show coding first ∈ subset from hfirst)
      exact (not_lt_of_ge (hdist.trans hdiam)) hdiameter
    exact (measure_mono hcontained).trans_eq (binaryBranchMeasure_cylinder depth first)
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty, measure_empty]
    exact bot_le

end LambdaCantor.Last
