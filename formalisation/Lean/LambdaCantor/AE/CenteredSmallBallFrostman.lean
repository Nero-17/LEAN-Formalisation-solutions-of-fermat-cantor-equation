import LambdaCantor.AE.CenteredSmallBallMeasure
import LambdaCantor.Last.BinaryFrostman

noncomputable section
open Set MeasureTheory Metric Filter
namespace LambdaCantor.AE

/-- Conditioning on the second address converts first-coordinate root
separation into an actual root-law Frostman bound. -/
theorem rootLaw_frostman_of_first_coordinate_separation
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    {contraction separation dimension : ℝ}
    (contraction_positive : 0 < contraction) (contraction_less_one : contraction < 1)
    (separation_positive : 0 < separation) (dimension_positive : 0 < dimension)
    (matching : contraction^dimension = (1/2 : ℝ))
    (separated : ∀ second : ℕ → Bool, ∀ depth : ℕ, ∀ first other : ℕ → Bool,
      (∃ position < depth, first position ≠ other position) →
      separation*contraction^depth ≤
        |root (fun index => (first index, second index)) - root (fun index => (other index, second index))|)
    {subset : Set ℝ} (subset_measurable : MeasurableSet subset)
    (small : ediam subset ≤ ENNReal.ofReal (separation/2)) :
    First.Roots.rootLaw root subset ≤
      ENNReal.ofReal ((2/(separation*contraction))^dimension) * ediam subset^dimension := by
  rw [rootLaw_eq_binary_product root root_measurable,
    Measure.map_apply (by fun_prop) subset_measurable,
    Measure.prod_apply_symm (subset_measurable.preimage (by fun_prop))]
  calc
    _ ≤ ∫⁻ _second, ENNReal.ofReal ((2/(separation*contraction))^dimension) * ediam subset^dimension
        ∂Last.binaryBranchMeasure := by
      apply lintegral_mono
      intro second
      have bound := Last.binary_pushforward_frostman
        (fun first : ℕ → Bool => root (fun index => (first index, second index)))
        (by fun_prop) contraction separation dimension contraction_positive contraction_less_one
        separation_positive dimension_positive matching
        (by
          intro depth first other different
          rw [edist_dist, Real.dist_eq]
          exact ENNReal.ofReal_le_ofReal (separated second depth first other different))
        subset_measurable small
      rw [Measure.map_apply (by fun_prop) subset_measurable] at bound
      exact bound
    _ = _ := by simp

end LambdaCantor.AE
