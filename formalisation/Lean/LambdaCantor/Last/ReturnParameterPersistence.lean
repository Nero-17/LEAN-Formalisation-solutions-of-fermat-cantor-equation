import LambdaCantor.Last.CompactStrictReturns
import LambdaCantor.Last.ReturnAtlas
import Mathlib.Topology.Compactness.Compact

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- Compactness gives one finite choice set and one margin that survive a
parameter change. Joint continuity is required only at the original compact
level family. -/
theorem compact_parameter_uniform_positive_margin {ι : Type*}
    {levels : Set ℝ} (hcompact : IsCompact levels) (hnonempty : levels.Nonempty)
    (parameter : ℝ) (score : ι → ℝ → ℝ → ℝ)
    (hcontinuous : ∀ index, Continuous (score index parameter))
    (hjoint : ∀ index level, level ∈ levels →
      ContinuousAt (fun pair : ℝ × ℝ => score index pair.1 pair.2) (parameter, level))
    (hpositive : ∀ level ∈ levels, ∃ index, 0 < score index parameter level) :
    ∃ (selected : Finset ι) (margin : ℝ), 0 < margin ∧
      ∀ᶠ perturbed in 𝓝 parameter, ∀ level ∈ levels,
        ∃ index ∈ selected, margin < score index perturbed level := by
  obtain ⟨selected, margin, neighborhood, hmargin, _, hsubset, hselected⟩ :=
    compact_uniform_positive_margin hcompact hnonempty (fun index => score index parameter)
      hcontinuous hpositive
  refine ⟨selected, margin / 2, by positivity, ?_⟩
  apply hcompact.eventually_forall_of_forall_eventually
  intro level hlevel
  obtain ⟨index, hindex, hscore⟩ := hselected level (hsubset hlevel)
  have heventual := continuousAt_const.eventually_lt (hjoint index level hlevel)
    (show margin / 2 < score index parameter level by linarith)
  filter_upwards [heventual] with pair hpair
  exact ⟨index, hindex, hpair⟩

theorem continuous_wordMap_zero_parameter (word : List (Bool × Bool)) :
    Continuous (fun ratio : ℝ => wordMap ratio word 0) := by
  induction word with
  | nil => exact continuous_const
  | cons digit rest induction_hypothesis =>
    change Continuous (fun ratio : ℝ => (1 - ratio) • digitPoint digit +
      ratio • wordMap ratio rest 0)
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul induction_hypothesis)

theorem continuousAt_parameter_linearWordReturn {ratio level : ℝ} (hratio : ratio ≠ 0)
    (linear : (ℝ × ℝ) →L[ℝ] ℝ) (word : List (Bool × Bool)) :
    ContinuousAt (fun pair : ℝ × ℝ =>
      linearWordReturn pair.1 linear.toLinearMap word pair.2) (ratio, level) := by
  have hcorner : Continuous (fun pair : ℝ × ℝ => linear (wordMap pair.1 word 0)) :=
    linear.continuous.comp ((continuous_wordMap_zero_parameter word).comp continuous_fst)
  exact (continuous_snd.sub hcorner).continuousAt.div
    (continuous_fst.pow word.length).continuousAt (pow_ne_zero _ hratio)

/-- The same finite word pairs and positive perturbation margin remain valid
on the compact returning set for all nearby contractions. -/
theorem compact_strict_returns_persist_parameter {ratio : ℝ} (hratio : ratio ≠ 0)
    (linear : (ℝ × ℝ) →L[ℝ] ℝ) (levels : Set ℝ)
    (hcompact : IsCompact levels) (hnonempty : levels.Nonempty)
    (hcomplement : levelsᶜ.Nonempty)
    (hreturns : ∀ level ∈ levels, ∃ pair : ReturnPair,
      linearWordReturn ratio linear.toLinearMap (pair.word false) level ∈ interior levels ∧
      linearWordReturn ratio linear.toLinearMap (pair.word true) level ∈ interior levels) :
    ∃ (selected : Finset ReturnPair) (margin : ℝ), 0 < margin ∧
      ∀ᶠ perturbed in 𝓝 ratio, ∀ level ∈ levels, ∃ pair ∈ selected,
        ∀ firstValue secondValue : ℝ,
          dist firstValue (linearWordReturn perturbed linear.toLinearMap (pair.word false) level) < margin →
          dist secondValue (linearWordReturn perturbed linear.toLinearMap (pair.word true) level) < margin →
          firstValue ∈ levels ∧ secondValue ∈ levels := by
  let score : ReturnPair → ℝ → ℝ → ℝ := fun pair contraction level =>
    min (Metric.infDist (linearWordReturn contraction linear.toLinearMap (pair.word false) level) levelsᶜ)
      (Metric.infDist (linearWordReturn contraction linear.toLinearMap (pair.word true) level) levelsᶜ)
  obtain ⟨selected, margin, hmargin, hpersist⟩ :=
    compact_parameter_uniform_positive_margin hcompact hnonempty ratio score
      (fun pair => ((Metric.continuous_infDist_pt _).comp
        (continuous_linearWordReturn ratio linear.toLinearMap _)).min
        ((Metric.continuous_infDist_pt _).comp (continuous_linearWordReturn ratio linear.toLinearMap _)))
      (fun pair level _ =>
        ((Metric.continuous_infDist_pt _).continuousAt.comp
          (continuousAt_parameter_linearWordReturn hratio linear (pair.word false))).min
        ((Metric.continuous_infDist_pt _).continuousAt.comp
          (continuousAt_parameter_linearWordReturn hratio linear (pair.word true))))
      (by
        intro level hlevel
        obtain ⟨pair, hfirst, hsecond⟩ := hreturns level hlevel
        refine ⟨pair, lt_min ?_ ?_⟩
        · apply (Metric.infDist_pos_iff_notMem_closure hcomplement).mp
          simpa only [closure_compl, Set.mem_compl_iff, not_not] using hfirst
        · apply (Metric.infDist_pos_iff_notMem_closure hcomplement).mp
          simpa only [closure_compl, Set.mem_compl_iff, not_not] using hsecond)
  refine ⟨selected, margin, hmargin, ?_⟩
  filter_upwards [hpersist] with perturbed hperturbed
  intro level hlevel
  obtain ⟨pair, hpair, hscore⟩ := hperturbed level hlevel
  refine ⟨pair, hpair, ?_⟩
  intro firstValue secondValue hfirst hsecond
  constructor
  · exact Metric.ball_infDist_compl_subset
      (Metric.mem_ball.mpr (hfirst.trans (lt_min_iff.mp hscore).1))
  · exact Metric.ball_infDist_compl_subset
      (Metric.mem_ball.mpr (hsecond.trans (lt_min_iff.mp hscore).2))

end LambdaCantor.Last
