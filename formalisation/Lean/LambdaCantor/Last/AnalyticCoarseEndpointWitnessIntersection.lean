import LambdaCantor.Last.AnalyticCoarsePerturbedLogPresentation
import LambdaCantor.Last.AnalyticCoarseGapLink
import LambdaCantor.Last.BinaryGapAffine

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

/-- A strict link persists for the actual power logarithm along every positive
sequence of scales tending to zero. The intersection is obtained from the
registered general Gap Lemma and actual defining sequences. -/
theorem coarse_actual_log_intersections_of_strict_link {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent : 1 < exponent) (hlink : CoarseStrictLogLink ratio exponent) :
    ∃ shift : ℤ, ∀ scales : ℕ → ℝ,
      (∀ index, 0 < scales index) → Tendsto scales atTop (𝓝 0) →
      ∀ᶠ index in atTop, ∃ first ∈ outerCantor ratio, ∃ second ∈ outerCantor ratio,
        0 < coarseNormalizedPowerDrop exponent (scales index) second ∧
        exponent * Real.log first = Real.log exponent - shift * (-Real.log ratio) +
          coarsePowerLog exponent (scales index) second := by
  obtain ⟨shift, value, hvalue, hstrict⟩ := hlink
  refine ⟨shift, ?_⟩
  intro scales hpositive hzero
  have hratio : 0 ≤ ratio := by linarith
  have hless : ratio < 1 := by linarith
  have hcomplement : 0 < 1 - ratio := by linarith
  have hexponent_positive : 0 < exponent := by linarith
  have hlog_negative : Real.log (1 - ratio) < 0 :=
    Real.log_neg hcomplement (by linarith)
  have hwithin : Tendsto scales atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
      (Eventually.of_forall hpositive)
  have hleft := (coarsePowerLog_limit hexponent_positive.ne' hcomplement).comp hwithin
  have hright := (coarsePowerLog_limit hexponent_positive.ne' (by norm_num : (0 : ℝ) < 1)).comp hwithin
  have hstrict_left : ∀ᶠ index in atTop,
      Real.log exponent - shift * (-Real.log ratio) +
          coarsePowerLog exponent (scales index) (1 - ratio) < exponent * value := by
    have hlimit := hleft.const_add (Real.log exponent - shift * (-Real.log ratio))
    exact hlimit.eventually (gt_mem_nhds hstrict.1)
  have hstrict_right : ∀ᶠ index in atTop,
      exponent * value < Real.log exponent - shift * (-Real.log ratio) +
        coarsePowerLog exponent (scales index) 1 := by
    have hlimit := hright.const_add (Real.log exponent - shift * (-Real.log ratio))
    simp only [Real.log_one, add_zero] at hlimit
    exact hlimit.eventually (lt_mem_nhds hstrict.2)
  have hwidth : ∀ᶠ index in atTop,
      coarsePowerLog exponent (scales index) 1 -
        coarsePowerLog exponent (scales index) (1 - ratio) ≤
          0 - exponent * Real.log (1 - ratio) := by
    have hlimit := hright.sub hleft
    have hstrict_width : Real.log (1 : ℝ) - Real.log (1 - ratio) <
        0 - exponent * Real.log (1 - ratio) := by
      rw [Real.log_one]
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr hexponent) hlog_negative]
    exact (hlimit.eventually (gt_mem_nhds hstrict_width)).mono fun _ h => h.le
  obtain ⟨cutoff, hcutoff, hpresentations⟩ :=
    coarsePerturbedOuterLogSet_binary_presentation hexponent hlower hupper
  obtain ⟨positiveCutoff, hpositiveCutoff, hdrop_positive⟩ :=
    coarsePowerLog_uniform_relative_derivative hexponent hcomplement (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hstrict_left, hstrict_right, hwidth,
    hzero.eventually (gt_mem_nhds hcutoff), hzero.eventually (gt_mem_nhds hpositiveCutoff)]
      with index hleft_strict hright_strict hwidth_le hsmall hsmall_positive
  obtain ⟨perturbed, hperturbed⟩ := hpresentations (scales index) (hpositive index) hsmall
  let translation := Real.log exponent - shift * (-Real.log ratio)
  let firstSet : Set ℝ := (fun point => exponent * point + 0) '' coarseOuterLogSet ratio
  let secondSet : Set ℝ := (fun point => 1 * point + translation) ''
    coarsePerturbedOuterLogSet exponent (scales index) ratio
  have hfirst_left : exponent * Real.log (1 - ratio) ∈ firstSet :=
    ⟨Real.log (1 - ratio), lower_mem_coarseOuterLogSet ratio, by simp⟩
  have hfirst_right : (0 : ℝ) ∈ firstSet :=
    ⟨0, zero_mem_coarseOuterLogSet hratio hless, by simp⟩
  have hsecond_left : coarsePowerLog exponent (scales index) (1 - ratio) + translation ∈ secondSet :=
    ⟨_, ⟨1 - ratio, lower_mem_outerCantor ratio, rfl⟩, by simp⟩
  have hsecond_right : coarsePowerLog exponent (scales index) 1 + translation ∈ secondSet :=
    ⟨_, ⟨1, one_mem_outerCantor hratio hless, rfl⟩, by simp⟩
  have hbounds := coarseOuterLogSet_bounds hratio hless hvalue
  have hpoint : exponent * value ∈ firstSet := ⟨value, hvalue, by simp⟩
  have hpoint_bounds : exponent * value ∈ Set.Icc (exponent * Real.log (1 - ratio)) 0 :=
    ⟨mul_le_mul_of_nonneg_left hbounds.1 hexponent_positive.le,
      by simpa only [mul_zero] using mul_le_mul_of_nonneg_left hbounds.2 hexponent_positive.le⟩
  have hnoncontainment := notContainedInGap_pair_of_strict_link
    hfirst_left hfirst_right hsecond_left hsecond_right
    (show (coarsePowerLog exponent (scales index) 1 + translation) -
        (coarsePowerLog exponent (scales index) (1 - ratio) + translation) ≤
        0 - exponent * Real.log (1 - ratio) by linarith)
    hpoint hpoint_bounds
    (show exponent * value ∈ Set.Ioo
      (coarsePowerLog exponent (scales index) (1 - ratio) + translation)
      (coarsePowerLog exponent (scales index) 1 + translation) by
        dsimp [translation]; constructor <;> linarith)
  have hfirst_bridges := (coarseOuterLogBinaryPresentation hlower hupper).affine_bridgeBound
    (scale := exponent) (offset := 0) hexponent_positive
    (coarseOuterLogBinaryPresentation_bridgeBound hlower hupper)
  have hsecond_bridges := perturbed.affine_bridgeBound
    (scale := 1) (offset := translation) (by norm_num) hperturbed
  obtain ⟨point, hfirst, hsecond⟩ := ExternalNewhouse.binary_defining_sequence_gap_lemma
    firstSet secondSet ((coarseOuterLogBinaryPresentation hlower hupper).affine exponent 0 hexponent_positive)
    (perturbed.affine 1 translation (by norm_num))
    (1 + 13 / 8000) (1 + 1 / 1000)
    (by norm_num) (by norm_num) (by norm_num)
    hfirst_bridges hsecond_bridges hnoncontainment.1 hnoncontainment.2
  obtain ⟨_, ⟨first, hfirst_mem, rfl⟩, hfirst_eq⟩ := hfirst
  obtain ⟨_, ⟨second, hsecond_mem, rfl⟩, hsecond_eq⟩ := hsecond
  have hsecond_bounds := outerCantor_bounds hratio hless hsecond_mem
  have hdrop := (hdrop_positive (scales index) (hpositive index) hsmall_positive second hsecond_bounds).1
  refine ⟨first, hfirst_mem, second, hsecond_mem, by linarith, ?_⟩
  change exponent * Real.log first + 0 = point at hfirst_eq
  change 1 * coarsePowerLog exponent (scales index) second + translation = point at hsecond_eq
  dsimp [translation] at hsecond_eq
  linarith

end LambdaCantor.Last
