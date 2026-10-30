import LambdaCantor.Last.CompactReturns
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section
namespace LambdaCantor.Last

/-- The finite uniform-margin conclusion used at the start of strict returns.
Each index represents a pair of words. Incomparability and nonempty lengths are
preserved by selecting indices; they are independent of this topological step. -/
theorem compact_strict_return_selection {ι : Type*} {levels : Set ℝ}
    (hcompact : IsCompact levels) (hnonempty : levels.Nonempty)
    (hcomplement : levelsᶜ.Nonempty)
    (firstReturn secondReturn : ι → ℝ → ℝ)
    (hfirst : ∀ index, Continuous (firstReturn index))
    (hsecond : ∀ index, Continuous (secondReturn index))
    (hreturns : ∀ level ∈ levels, ∃ index,
      firstReturn index level ∈ interior levels ∧ secondReturn index level ∈ interior levels) :
    ∃ (selected : Finset ι) (margin : ℝ) (neighborhood : Set ℝ),
      0 < margin ∧ IsOpen neighborhood ∧ levels ⊆ neighborhood ∧
      ∀ level ∈ neighborhood, ∃ index ∈ selected,
        ∀ firstValue secondValue : ℝ,
          dist firstValue (firstReturn index level) < margin →
          dist secondValue (secondReturn index level) < margin →
          firstValue ∈ levels ∧ secondValue ∈ levels := by
  obtain ⟨selected, margin, neighborhood, hmargin, hopen, hsubset, hselected⟩ :=
    compact_uniform_positive_margin hcompact hnonempty
      (fun index level => min (Metric.infDist (firstReturn index level) levelsᶜ)
        (Metric.infDist (secondReturn index level) levelsᶜ))
      (fun index => ((Metric.continuous_infDist_pt _).comp (hfirst index)).min
        ((Metric.continuous_infDist_pt _).comp (hsecond index)))
      (by
        intro level hlevel
        obtain ⟨index, hreturnFirst, hreturnSecond⟩ := hreturns level hlevel
        refine ⟨index, lt_min ?_ ?_⟩
        · apply (Metric.infDist_pos_iff_notMem_closure hcomplement).mp
          simpa only [closure_compl, Set.mem_compl_iff, not_not] using hreturnFirst
        · apply (Metric.infDist_pos_iff_notMem_closure hcomplement).mp
          simpa only [closure_compl, Set.mem_compl_iff, not_not] using hreturnSecond)
  refine ⟨selected, margin, neighborhood, hmargin, hopen, hsubset, ?_⟩
  intro level hlevel
  obtain ⟨index, hindex, hscore⟩ := hselected level hlevel
  refine ⟨index, hindex, ?_⟩
  intro firstValue secondValue hperturbFirst hperturbSecond
  constructor
  · apply Metric.ball_infDist_compl_subset
    exact Metric.mem_ball.mpr (hperturbFirst.trans (lt_min_iff.mp hscore).1)
  · apply Metric.ball_infDist_compl_subset
    exact Metric.mem_ball.mpr (hperturbSecond.trans (lt_min_iff.mp hscore).2)

end LambdaCantor.Last
