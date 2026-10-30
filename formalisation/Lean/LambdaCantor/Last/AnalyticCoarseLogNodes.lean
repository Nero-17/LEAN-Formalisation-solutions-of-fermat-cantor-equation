import LambdaCantor.Last.ScalarCylinders
import LambdaCantor.Last.AnalyticCoarseLogCylinderGeometry
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

def coarseRawNode (ratio : ℝ) (word : List Bool) (coordinate : ℝ) : ℝ :=
  1 - ratio + ratio * scalarWordMap ratio word coordinate

def coarseLogNode (ratio : ℝ) (word : List Bool) (coordinate : ℝ) : ℝ :=
  Real.log (coarseRawNode ratio word coordinate)

theorem coarseRawNode_bounds {ratio coordinate : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (word : List Bool)
    (hcoordinate : coordinate ∈ Set.Icc (0 : ℝ) 1) :
    coarseRawNode ratio word coordinate ∈ Set.Icc (1 - ratio) 1 := by
  have hbounds := scalarWordMap_bounds hratio hless word hcoordinate
  dsimp [coarseRawNode]
  constructor <;> nlinarith [mul_nonneg hratio hbounds.1,
    mul_le_mul_of_nonneg_left hbounds.2 hratio]

theorem coarseRawNode_affine (ratio : ℝ) (word : List Bool) (coordinate : ℝ) :
    coarseRawNode ratio word coordinate =
      coarseRawNode ratio word 0 + ratio ^ (word.length + 1) * coordinate := by
  dsimp [coarseRawNode]
  rw [scalarWordMap_affine ratio word coordinate, pow_succ]
  ring

theorem coarseRawNode_strictMono {ratio : ℝ} (hratio : 0 < ratio) (word : List Bool) :
    StrictMono (coarseRawNode ratio word) := by
  intro first second hless
  rw [coarseRawNode_affine ratio word first, coarseRawNode_affine ratio word second]
  exact add_lt_add_of_le_of_lt (le_refl _) (mul_lt_mul_of_pos_left hless (pow_pos hratio _))

theorem coarseLogNode_strictMonoOn {ratio : ℝ}
    (hratio : 0 < ratio) (hless : ratio < 1) (word : List Bool) :
    StrictMonoOn (coarseLogNode ratio word) (Set.Icc 0 1) := by
  intro first hfirst second hsecond horder
  apply Real.strictMonoOn_log
  · have := (coarseRawNode_bounds hratio.le hless word hfirst).1
    change 0 < coarseRawNode ratio word first
    linarith
  · have := (coarseRawNode_bounds hratio.le hless word hsecond).1
    change 0 < coarseRawNode ratio word second
    linarith
  · exact coarseRawNode_strictMono hratio word horder

theorem coarseLogNode_width_bound {ratio : ℝ}
    (hratio : 0 < ratio) (hless : ratio < 1) (word : List Bool) :
    coarseLogNode ratio word 1 - coarseLogNode ratio word 0 ≤
      ratio ^ (word.length + 1) / (1 - ratio) := by
  have hzero := coarseRawNode_bounds hratio.le hless word (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
  have hone := coarseRawNode_bounds hratio.le hless word (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hzero_positive : 0 < coarseRawNode ratio word 0 := by linarith [hzero.1]
  have hone_positive : 0 < coarseRawNode ratio word 1 := by linarith [hone.1]
  have horder : coarseRawNode ratio word 0 ≤ coarseRawNode ratio word 1 :=
    (coarseRawNode_strictMono hratio word (by norm_num : (0 : ℝ) < 1)).le
  have hbound := (coarse_log_interval_bounds hratio.le hless hzero.1 horder hone.2).2
  rw [Real.log_div hone_positive.ne' hzero_positive.ne'] at hbound
  have hwidth : coarseRawNode ratio word 1 - coarseRawNode ratio word 0 =
      ratio ^ (word.length + 1) := by
    rw [coarseRawNode_affine ratio word 1]
    ring
  simpa only [coarseLogNode, hwidth] using hbound

theorem coarseLogNode_mesh {ratio : ℝ} (hratio : 0 < ratio) (hless : ratio < 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ depth : ℕ, ∀ word : List Bool, depth ≤ word.length →
      coarseLogNode ratio word 1 - coarseLogNode ratio word 0 < epsilon := by
  have hone : 0 < 1 - ratio := by linarith
  have hlimit : Tendsto (fun depth : ℕ => ratio ^ depth) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio.le hless
  have hevent := hlimit.eventually (gt_mem_nhds (mul_pos hepsilon hone))
  obtain ⟨depth, hdepth⟩ := eventually_atTop.mp hevent
  refine ⟨depth, ?_⟩
  intro word hword
  exact (coarseLogNode_width_bound hratio hless word).trans_lt
    ((div_lt_iff₀ hone).mpr (hdepth (word.length + 1) (by omega)))

theorem coarseLogNode_left_child (ratio : ℝ) (word : List Bool) :
    coarseLogNode ratio (word ++ [false]) 0 = coarseLogNode ratio word 0 := by
  simp [coarseLogNode, coarseRawNode, scalarWordMap_append, scalarWordMap]

theorem coarseLogNode_right_child (ratio : ℝ) (word : List Bool) :
    coarseLogNode ratio (word ++ [true]) 1 = coarseLogNode ratio word 1 := by
  simp [coarseLogNode, coarseRawNode, scalarWordMap_append, scalarWordMap]

theorem coarseLogNode_gap_left (ratio : ℝ) (word : List Bool) :
    coarseLogNode ratio (word ++ [false]) 1 = coarseLogNode ratio word ratio := by
  simp [coarseLogNode, coarseRawNode, scalarWordMap_append, scalarWordMap]

theorem coarseLogNode_gap_right (ratio : ℝ) (word : List Bool) :
    coarseLogNode ratio (word ++ [true]) 0 = coarseLogNode ratio word (1 - ratio) := by
  simp [coarseLogNode, coarseRawNode, scalarWordMap_append, scalarWordMap]

end LambdaCantor.Last
