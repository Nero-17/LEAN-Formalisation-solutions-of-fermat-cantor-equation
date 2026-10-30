import LambdaCantor.Last.AnalyticCoarseLogLimit
import LambdaCantor.Last.ExternalNewhouseBinary

noncomputable section
namespace LambdaCantor.Last

theorem coarseLogNode_bridge_bounds {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) (word : List Bool) :
    (1 + 13 / 8000) * (coarseLogNode ratio (word ++ [true]) 0 -
      coarseLogNode ratio (word ++ [false]) 1) ≤
        coarseLogNode ratio (word ++ [false]) 1 - coarseLogNode ratio word 0 ∧
    (1 + 13 / 8000) * (coarseLogNode ratio (word ++ [true]) 0 -
      coarseLogNode ratio (word ++ [false]) 1) ≤
        coarseLogNode ratio word 1 - coarseLogNode ratio (word ++ [true]) 0 := by
  have hratio : 0 < ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hzero := coarseRawNode_bounds hratio.le hless word (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
  have hzero_positive : 0 < coarseRawNode ratio word 0 := by linarith [hzero.1]
  have hfirst_positive : 0 < coarseRawNode ratio word ratio := by
    have := (coarseRawNode_bounds (coordinate := ratio) hratio.le hless word
      ⟨hratio.le, hless.le⟩).1
    linarith
  have hmiddle_positive : 0 < coarseRawNode ratio word (1 - ratio) := by
    have := (coarseRawNode_bounds (coordinate := 1 - ratio) hratio.le hless word
      (show 1 - ratio ∈ Set.Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)).1
    linarith
  have htop_positive : 0 < coarseRawNode ratio word 1 := by
    have := (coarseRawNode_bounds hratio.le hless word (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)).1
    linarith
  have hwidth_upper : ratio ^ (word.length + 1) ≤ ratio := by
    have hpower : ratio ^ word.length ≤ 1 := pow_le_one₀ hratio.le hless.le
    simpa only [pow_succ, one_mul] using mul_le_mul_of_nonneg_right hpower hratio.le
  have hbound := coarse_log_cylinder_bridge_bounds hlower hupper hzero.1
    (pow_nonneg hratio.le _) hwidth_upper
  have hfirst : coarseRawNode ratio word 0 + ratio * ratio ^ (word.length + 1) =
      coarseRawNode ratio word ratio := by
    rw [coarseRawNode_affine ratio word ratio]
    ring
  have hmiddle : coarseRawNode ratio word 0 + (1 - ratio) * ratio ^ (word.length + 1) =
      coarseRawNode ratio word (1 - ratio) := by
    rw [coarseRawNode_affine ratio word (1 - ratio)]
    ring
  have htop : coarseRawNode ratio word 0 + ratio ^ (word.length + 1) =
      coarseRawNode ratio word 1 := by
    rw [coarseRawNode_affine ratio word 1]
    ring
  rw [hfirst, hmiddle, htop,
    Real.log_div hmiddle_positive.ne' hfirst_positive.ne',
    Real.log_div hfirst_positive.ne' hzero_positive.ne',
    Real.log_div htop_positive.ne' hmiddle_positive.ne'] at hbound
  rw [coarseLogNode_gap_left, coarseLogNode_gap_right]
  exact hbound

/-- The actual logarithmic outer Cantor set with all defining-sequence data
proved internally. The external Gap Lemma is not used to construct it. -/
def coarseOuterLogBinaryPresentation {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    ExternalNewhouse.BinaryGapPresentation (coarseOuterLogSet ratio) where
  left := fun word => coarseLogNode ratio word 0
  right := fun word => coarseLogNode ratio word 1
  node_order := by
    intro word
    exact coarseLogNode_strictMonoOn (by linarith) (by linarith) word
      (by norm_num) (by norm_num) (by norm_num)
  left_coherent := coarseLogNode_left_child ratio
  right_coherent := coarseLogNode_right_child ratio
  children_order := by
    intro word
    rw [coarseLogNode_gap_left, coarseLogNode_gap_right]
    have hmonotone := coarseLogNode_strictMonoOn
      (show 0 < ratio by linarith) (show ratio < 1 by linarith) word
    have hratio : ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hcomplement : 1 - ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    exact ⟨hmonotone (by norm_num) hratio (by linarith),
      hmonotone hratio hcomplement (by linarith),
      hmonotone hcomplement (by norm_num) (by linarith)⟩
  limit_set := coarseOuterLogSet_eq_binary_limit (by linarith) (by linarith)
  mesh := by
    intro epsilon hepsilon
    exact coarseLogNode_mesh (by linarith) (by linarith) hepsilon

theorem coarseOuterLogBinaryPresentation_bridgeBound {ratio : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2) :
    (coarseOuterLogBinaryPresentation hlower hupper).bridgeBound (1 + 13 / 8000) := by
  intro word
  exact coarseLogNode_bridge_bounds hlower hupper word

end LambdaCantor.Last
