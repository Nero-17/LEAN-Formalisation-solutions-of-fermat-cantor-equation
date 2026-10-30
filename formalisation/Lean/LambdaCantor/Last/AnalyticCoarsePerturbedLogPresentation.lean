import LambdaCantor.Last.AnalyticCoarsePerturbedLog
import LambdaCantor.Last.AnalyticCoarseLogPresentation
import LambdaCantor.Last.BinaryGapMonotoneImage

noncomputable section
namespace LambdaCantor.Last

/-- The actual outer Cantor image under the normalized power logarithm. -/
def coarsePerturbedOuterLogSet (exponent scale ratio : ℝ) : Set ℝ :=
  coarsePowerLog exponent scale '' outerCantor ratio

theorem coarsePerturbedOuterLogSet_eq_image {ratio : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (exponent scale : ℝ) :
    coarsePerturbedOuterLogSet exponent scale ratio =
      coarseLogCoordinateMap exponent scale '' coarseOuterLogSet ratio := by
  ext value
  constructor
  · rintro ⟨point, hpoint, rfl⟩
    have hbounds := outerCantor_bounds hratio hless hpoint
    have hpositive : 0 < point := by linarith [hbounds.1]
    refine ⟨Real.log point, ⟨point, hpoint, rfl⟩, ?_⟩
    simp only [coarseLogCoordinateMap, Real.exp_log hpositive]
  · rintro ⟨_, ⟨point, hpoint, rfl⟩, rfl⟩
    have hbounds := outerCantor_bounds hratio hless hpoint
    have hpositive : 0 < point := by linarith [hbounds.1]
    refine ⟨point, hpoint, ?_⟩
    simp only [coarseLogCoordinateMap, Real.exp_log hpositive]

/-- Quantitative C1 transport applies to the actual normalized power drop.
Both the map and its increment bounds have been constructed above. -/
theorem coarsePerturbedOuterLogSet_binary_presentation {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    ∃ cutoff > 0, ∀ scale : ℝ, 0 < scale → scale < cutoff →
      ∃ presentation : ExternalNewhouse.BinaryGapPresentation
          (coarsePerturbedOuterLogSet exponent scale ratio),
        presentation.bridgeBound (1 + 1 / 1000) := by
  have hratio : 0 ≤ ratio := by linarith
  have hless : ratio < 1 := by linarith
  obtain ⟨cutoff, hcutoff, hincrements⟩ := coarseLogCoordinateMap_uniform_increments
    hexponent hratio hless (by norm_num : (0 : ℝ) < 1 / 4000)
  refine ⟨cutoff, hcutoff, ?_⟩
  intro scale hscale hsmall
  have hestimates := hincrements scale hscale hsmall
  have hroot : Set.Icc ((coarseOuterLogBinaryPresentation hlower hupper).left [])
      ((coarseOuterLogBinaryPresentation hlower hupper).right []) =
      Set.Icc (Real.log (1 - ratio)) 0 := by
    change Set.Icc (Real.log (1 - ratio + ratio * 0))
      (Real.log (1 - ratio + ratio * 1)) = _
    simp
  have hcontinuous : ContinuousOn (coarseLogCoordinateMap exponent scale)
      (Set.Icc ((coarseOuterLogBinaryPresentation hlower hupper).left [])
        ((coarseOuterLogBinaryPresentation hlower hupper).right [])) := by
    rw [hroot]
    exact hestimates.1
  have hbound : ∀ first ∈ Set.Icc ((coarseOuterLogBinaryPresentation hlower hupper).left [])
        ((coarseOuterLogBinaryPresentation hlower hupper).right []),
      ∀ second ∈ Set.Icc ((coarseOuterLogBinaryPresentation hlower hupper).left [])
        ((coarseOuterLogBinaryPresentation hlower hupper).right []), first ≤ second →
        (1 - 1 / 4000) * (second - first) ≤
          coarseLogCoordinateMap exponent scale second - coarseLogCoordinateMap exponent scale first ∧
        coarseLogCoordinateMap exponent scale second - coarseLogCoordinateMap exponent scale first ≤
          (1 + 1 / 4000) * (second - first) := by
    rw [hroot]
    exact hestimates.2
  rw [coarsePerturbedOuterLogSet_eq_image hratio hless]
  let presentation := (coarseOuterLogBinaryPresentation hlower hupper).monotoneImage
    (coarseLogCoordinateMap exponent scale)
    (by norm_num : (0 : ℝ) < 1 - 1 / 4000)
    (by norm_num : (0 : ℝ) < 1 + 1 / 4000) hcontinuous hbound
  refine ⟨presentation, ?_⟩
  have htransport := (coarseOuterLogBinaryPresentation hlower hupper).monotoneImage_bridgeBound
    (coarseLogCoordinateMap exponent scale)
    (by norm_num : (0 : ℝ) < 1 - 1 / 4000)
    (by norm_num : (0 : ℝ) < 1 + 1 / 4000)
    (by norm_num : (0 : ℝ) ≤ 1 + 13 / 8000)
    hcontinuous hbound (coarseOuterLogBinaryPresentation_bridgeBound hlower hupper)
  have hconstant : (1 + 1 / 1000 : ℝ) ≤
      (1 + 13 / 8000) * (1 - 1 / 4000) / (1 + 1 / 4000) := by norm_num
  intro word
  have hgap : 0 ≤ presentation.left (word ++ [true]) - presentation.right (word ++ [false]) :=
    sub_nonneg.mpr (presentation.children_order word).2.1.le
  have hsmaller := mul_le_mul_of_nonneg_right hconstant hgap
  exact ⟨hsmaller.trans (htransport word).1, hsmaller.trans (htransport word).2⟩

end LambdaCantor.Last
