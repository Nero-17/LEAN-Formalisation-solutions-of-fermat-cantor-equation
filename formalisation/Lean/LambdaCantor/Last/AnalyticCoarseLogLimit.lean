import LambdaCantor.Last.AnalyticCoarseLogNodes
import LambdaCantor.Last.AnalyticCoarseLogSet

noncomputable section
namespace LambdaCantor.Last

theorem isCompact_coarseOuterLogSet {ratio : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) : IsCompact (coarseOuterLogSet ratio) := by
  apply (isCompact_outerCantor hratio hless).image_of_continuousOn
  intro point hpoint
  have hpositive : 0 < point := by
    have := (outerCantor_bounds hratio hless hpoint).1
    linarith
  exact (Real.continuousAt_log hpositive.ne').continuousWithinAt

theorem coarseLogNode_zero_mem {ratio : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (word : List Bool) :
    coarseLogNode ratio word 0 ∈ coarseOuterLogSet ratio := by
  refine ⟨coarseRawNode ratio word 0, ?_, rfl⟩
  exact ⟨scalarWordMap ratio word 0,
    scalarWordMap_mem_cantorSet hratio hless word (zero_mem_cantorSet ratio), rfl⟩

/-- Exact equality with the binary limit set; this is an equality for the
actual logarithmic Cantor image, not a replacement by its convex hull. -/
theorem coarseOuterLogSet_eq_binary_limit {ratio : ℝ}
    (hratio : 0 < ratio) (hless : ratio < 1) :
    coarseOuterLogSet ratio = {point | ∀ depth : ℕ, ∃ word : List Bool,
      word.length = depth ∧
        point ∈ Set.Icc (coarseLogNode ratio word 0) (coarseLogNode ratio word 1)} := by
  ext point
  constructor
  · rintro ⟨raw, ⟨coordinate, hcoordinate, rfl⟩, rfl⟩ depth
    obtain ⟨word, hlength, tail, htail, hequation⟩ :=
      exists_scalar_cylinder hratio.le hless depth hcoordinate
    have htail_bounds := cantorSet_subset_unitInterval hratio.le hless htail
    have hmonotone := (coarseLogNode_strictMonoOn hratio hless word).monotoneOn
    refine ⟨word, hlength, ?_⟩
    have hfirst := hmonotone (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) htail_bounds htail_bounds.1
    have hsecond := hmonotone htail_bounds (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) htail_bounds.2
    simpa only [Set.mem_Icc, coarseLogNode, coarseRawNode, hequation] using And.intro hfirst hsecond
  · intro hpoint
    have hclosure : point ∈ closure (coarseOuterLogSet ratio) := by
      apply Metric.mem_closure_iff.mpr
      intro epsilon hepsilon
      obtain ⟨depth, hmesh⟩ := coarseLogNode_mesh hratio hless hepsilon
      obtain ⟨word, hlength, hbounds⟩ := hpoint depth
      refine ⟨coarseLogNode ratio word 0, coarseLogNode_zero_mem hratio.le hless word, ?_⟩
      have hwidth := hmesh word (by omega)
      have hdist : dist point (coarseLogNode ratio word 0) =
          point - coarseLogNode ratio word 0 := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hbounds.1)]
      rw [hdist]
      linarith [hbounds.2]
    simpa only [(isCompact_coarseOuterLogSet hratio.le hless).isClosed.closure_eq] using hclosure

end LambdaCantor.Last
