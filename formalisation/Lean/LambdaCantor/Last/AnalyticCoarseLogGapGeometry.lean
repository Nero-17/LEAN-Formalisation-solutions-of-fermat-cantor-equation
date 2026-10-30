import LambdaCantor.Last.AnalyticCoarseLogPresentation
import LambdaCantor.Last.AnalyticCoarseGapBounds
import LambdaCantor.Last.BinaryGapBasics

noncomputable section
namespace LambdaCantor.Last

theorem coarseLogNode_one_mem {ratio : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (word : List Bool) :
    coarseLogNode ratio word 1 ∈ coarseOuterLogSet ratio := by
  refine ⟨coarseRawNode ratio word 1, ?_, rfl⟩
  exact ⟨scalarWordMap ratio word 1,
    scalarWordMap_mem_cantorSet hratio hless word (one_mem_cantorSet hratio hless), rfl⟩

theorem coarseLogNode_gap_width_bound {ratio : ℝ}
    (hratio : 0 < ratio) (hupper : ratio < 1 / 2) (word : List Bool) :
    coarseLogNode ratio word (1 - ratio) - coarseLogNode ratio word ratio ≤
      ratio ^ (word.length + 1) * (1 - 2 * ratio) / (1 - ratio) := by
  have hless : ratio < 1 := by linarith
  have hfirst := coarseRawNode_bounds (coordinate := ratio) hratio.le hless word
    ⟨hratio.le, hless.le⟩
  have hsecond := coarseRawNode_bounds (coordinate := 1 - ratio) hratio.le hless word
    ⟨by linarith, by linarith⟩
  have hfirst_positive : 0 < coarseRawNode ratio word ratio := by linarith [hfirst.1]
  have hsecond_positive : 0 < coarseRawNode ratio word (1 - ratio) := by linarith [hsecond.1]
  have horder := (coarseRawNode_strictMono hratio word (show ratio < 1 - ratio by linarith)).le
  have hbound := (coarse_log_interval_bounds hratio.le hless hfirst.1 horder hsecond.2).2
  rw [Real.log_div hsecond_positive.ne' hfirst_positive.ne'] at hbound
  have hwidth : coarseRawNode ratio word (1 - ratio) - coarseRawNode ratio word ratio =
      ratio ^ (word.length + 1) * (1 - 2 * ratio) := by
    rw [coarseRawNode_affine ratio word (1 - ratio), coarseRawNode_affine ratio word ratio]
    ring
  rw [hwidth] at hbound
  exact hbound

theorem coarseLogNode_nonroot_gap_lt {ratio : ℝ}
    (hratio : 0 < ratio) (hupper : ratio < 1 / 2) (word : List Bool)
    (hdepth : 1 ≤ word.length) :
    coarseLogNode ratio word (1 - ratio) - coarseLogNode ratio word ratio < 2 / 27 := by
  have hone : 0 < 1 - ratio := by linarith
  have hpower : ratio ^ (word.length + 1) ≤ ratio ^ 2 :=
    pow_le_pow_of_le_one hratio.le (by linarith) (by omega)
  have hscaled := mul_le_mul_of_nonneg_right hpower (show 0 ≤ 1 - 2 * ratio by linarith)
  have hbound := (coarseLogNode_gap_width_bound hratio hupper word).trans
    (div_le_div_of_nonneg_right hscaled hone.le)
  have hmaximum : ratio ^ 2 * (1 - 2 * ratio) ≤ 1 / 27 := by
    have hcertificate := mul_nonneg (sq_nonneg (ratio - 1 / 3))
      (show 0 ≤ 2 * ratio + 1 / 3 by linarith)
    nlinarith
  apply hbound.trans_lt
  apply (div_lt_iff₀ hone).mpr
  nlinarith

theorem coarseLogNode_deep_gap_lt {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) (word : List Bool)
    (hdepth : 2 ≤ word.length) :
    coarseLogNode ratio word (1 - ratio) - coarseLogNode ratio word ratio <
      (-Real.log (1 - ratio)) / 20 := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hpower : ratio ^ (word.length + 1) ≤ ratio ^ 3 :=
    pow_le_pow_of_le_one hratio.le (by linarith) (by omega)
  have hscaled := mul_le_mul_of_nonneg_right hpower (show 0 ≤ 1 - 2 * ratio by linarith)
  have hbound := (coarseLogNode_gap_width_bound hratio hupper word).trans
    (div_le_div_of_nonneg_right hscaled hone.le)
  have hconstant : ratio ^ 3 * (1 - 2 * ratio) / (1 - ratio) < 45569 / 2000000 := by
    apply (div_lt_iff₀ hone).mpr
    nlinarith [coarse_deep_log_gap_certificate hlower hupper.le]
  have hhull := (coarse_log_hull_period_bounds hlower hupper).1
  exact (hbound.trans_lt hconstant).trans (by linarith)

/-- Every actual empty interval inside the logarithmic hull is contained in
one explicit gap of the actual Cantor set. Endpoint contacts are retained. -/
theorem coarse_log_empty_interval_in_gap {ratio left right : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hleft : Real.log (1 - ratio) ≤ left) (hright : right ≤ 0) (horder : left < right)
    (hempty : ∀ point ∈ coarseOuterLogSet ratio, point ∉ Set.Ioo left right) :
    ∃ word : List Bool,
      coarseLogNode ratio word ratio ≤ left ∧ right ≤ coarseLogNode ratio word (1 - ratio) := by
  have hratio : 0 ≤ ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hmid_left : left < (left + right) / 2 := by linarith
  have hmid_right : (left + right) / 2 < right := by linarith
  let presentation := coarseOuterLogBinaryPresentation hlower hupper
  have hmid_hull : (left + right) / 2 ∈
      Set.Icc (presentation.left []) (presentation.right []) := by
    change (left + right) / 2 ∈ Set.Icc (coarseLogNode ratio [] 0) (coarseLogNode ratio [] 1)
    simpa [coarseLogNode, coarseRawNode, scalarWordMap] using
      (show (left + right) / 2 ∈ Set.Icc (Real.log (1 - ratio)) 0 from
        ⟨by linarith, by linarith⟩)
  have hmid_outside : (left + right) / 2 ∉ coarseOuterLogSet ratio := by
    intro hmem
    exact hempty _ hmem ⟨hmid_left, hmid_right⟩
  obtain ⟨word, hgap⟩ := presentation.exists_gap hmid_hull hmid_outside
  change (left + right) / 2 ∈ Set.Ioo
    (coarseLogNode ratio (word ++ [false]) 1) (coarseLogNode ratio (word ++ [true]) 0) at hgap
  have hgap_left : coarseLogNode ratio (word ++ [false]) 1 ≤ left := by
    by_contra hfailure
    exact hempty _ (coarseLogNode_one_mem hratio hless _) ⟨lt_of_not_ge hfailure, hgap.1.trans hmid_right⟩
  have hgap_right : right ≤ coarseLogNode ratio (word ++ [true]) 0 := by
    by_contra hfailure
    exact hempty _ (coarseLogNode_zero_mem hratio hless _) ⟨hmid_left.trans hgap.2, lt_of_not_ge hfailure⟩
  refine ⟨word, ?_, ?_⟩
  · simpa only [coarseLogNode_gap_left] using hgap_left
  · simpa only [coarseLogNode_gap_right] using hgap_right

end LambdaCantor.Last
