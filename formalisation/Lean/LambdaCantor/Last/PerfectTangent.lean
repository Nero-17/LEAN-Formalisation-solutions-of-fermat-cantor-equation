import LambdaCantor.Last.PerfectBranching
import LambdaCantor.Last.OverlapTangent

noncomputable section
namespace LambdaCantor.Last

/-- The analytic perfect-fibre transfer, with the affine return construction
kept explicit. The source of the perfect set can be arithmetic or geometric. -/
theorem perfect_fibre_positive_dimension_of_strict_returns
    {ratio slope : ℝ} (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hslope : 0 ≤ slope) (hcore : (affineOverlapCore ratio slope).Nonempty)
    (hreturns : ∀ value ∈ affineOverlapCore ratio slope, ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) value ∈
        interior (affineOverlapCore ratio slope) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) value ∈
        interior (affineOverlapCore ratio slope))
    (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (perfectSubset : Set (ℝ × ℝ)) (hperfect : Perfect perfectSubset)
    (hsubset : perfectSubset ⊆ {value | value ∈ cantorDust ratio ∧ function value = level})
    {point : ℝ × ℝ} (hpoint : point ∈ perfectSubset)
    (hderivative : HasStrictFDerivAt function (positiveLinearContinuous slope) point) :
    0 < dimH {value : ℝ × ℝ | value ∈ cantorDust ratio ∧ function value = level} := by
  apply positive_dimension_of_tangent_branching_overlap hpositive hhalf hslope hcore hreturns
    function level point hderivative
  exact perfect_fibre_deep_branching hpositive hhalf function level perfectSubset
    hperfect hsubset hpoint

end LambdaCantor.Last
