import LambdaCantor.Last.BinaryFrostman

noncomputable section
open MeasureTheory Metric
open scoped ENNReal NNReal
namespace LambdaCantor.Last

/-- A measurable binary coding with uniform geometric prefix separation forces
positive dimension of every measurable set containing its image. -/
theorem positive_dimension_of_separated_binary_coding
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (coding : (ℕ → Bool) → X) (hmeasurable : Measurable coding)
    (ratio separation : ℝ) (hratio : 0 < ratio) (hratio_one : ratio < 1)
    (hseparation : 0 < separation)
    (hseparated : ∀ depth : ℕ, ∀ first second : ℕ → Bool,
      (∃ position < depth, first position ≠ second position) →
      ENNReal.ofReal (separation * ratio ^ depth) ≤ edist (coding first) (coding second))
    {support : Set X} (hsupport : MeasurableSet support)
    (himage : ∀ branch, coding branch ∈ support) : 0 < dimH support := by
  have hexponent := binary_exponent_positive hratio hratio_one
  have hmatching := binary_exponent_rpow hratio hratio_one
  have hconstant : 0 < (2 / (separation * ratio)) ^
      (Real.log (1 / 2) / Real.log ratio) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hmass : binaryBranchMeasure.map coding support ≠ 0 := by
    rw [Measure.map_apply hmeasurable hsupport]
    have hpreimage : coding ⁻¹' support = Set.univ := by
      ext branch
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact himage branch
    rw [hpreimage, measure_univ]
    exact one_ne_zero
  have hdimension := dimension_lower_bound_of_closed_mass_distribution
    (binaryBranchMeasure.map coding)
    (⟨Real.log (1 / 2) / Real.log ratio, hexponent.le⟩ : ℝ≥0)
    (ENNReal.ofReal (separation / 2))
    (ENNReal.ofReal ((2 / (separation * ratio)) ^ (Real.log (1 / 2) / Real.log ratio)))
    (ENNReal.ofReal_pos.mpr (by linarith))
    (ne_of_gt (ENNReal.ofReal_pos.mpr hconstant)) ENNReal.ofReal_ne_top
    (fun subset hclosed hsmall => binary_pushforward_frostman coding hmeasurable
      ratio separation (Real.log (1 / 2) / Real.log ratio)
      hratio hratio_one hseparation hexponent hmatching hseparated
      hclosed.measurableSet hsmall) hmass
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr hexponent) hdimension

end LambdaCantor.Last
