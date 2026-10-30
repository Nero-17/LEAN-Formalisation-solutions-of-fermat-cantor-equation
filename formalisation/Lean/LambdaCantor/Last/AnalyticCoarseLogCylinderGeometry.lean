import LambdaCantor.Last.AnalyticCoarseLogBridges
import LambdaCantor.Last.AnalyticCoarseLogBridgesLeft

noncomputable section
namespace LambdaCantor.Last

theorem coarse_log_cylinder_bridge_bounds {ratio left width : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hleft : 1 - ratio ≤ left) (hwidth : 0 ≤ width) (hwidth_upper : width ≤ ratio) :
    (1 + 13 / 8000) * Real.log
      ((left + (1 - ratio) * width) / (left + ratio * width)) ≤
        Real.log ((left + ratio * width) / left) ∧
    (1 + 13 / 8000) * Real.log
      ((left + (1 - ratio) * width) / (left + ratio * width)) ≤
        Real.log ((left + width) / (left + (1 - ratio) * width)) := by
  have hratio : 0 < ratio := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hleft_positive : 0 < left := by linarith
  have hrelative : 0 ≤ width / left := div_nonneg hwidth hleft_positive.le
  have hrelative_upper : width / left ≤ ratio / (1 - ratio) := by
    calc
      _ ≤ ratio / left := div_le_div_of_nonneg_right hwidth_upper hleft_positive.le
      _ ≤ _ := div_le_div_of_nonneg_left hratio.le hone hleft
  have hleft_identity : (left + ratio * width) / left = 1 + ratio * (width / left) := by
    rw [add_div, div_self hleft_positive.ne', mul_div_assoc]
  have hmiddle_identity :
      (left + (1 - ratio) * width) / left = 1 + (1 - ratio) * (width / left) := by
    rw [add_div, div_self hleft_positive.ne', mul_div_assoc]
  have htop_identity : (left + width) / left = 1 + width / left := by
    rw [add_div, div_self hleft_positive.ne']
  have hgap_identity :
      (left + (1 - ratio) * width) / (left + ratio * width) =
      (1 + (1 - ratio) * (width / left)) / (1 + ratio * (width / left)) := by
    rw [← hmiddle_identity, ← hleft_identity]
    exact (div_div_div_cancel_right₀ hleft_positive.ne' _ _).symm
  have hright_identity : (left + width) / (left + (1 - ratio) * width) =
      (1 + width / left) / (1 + (1 - ratio) * (width / left)) := by
    rw [← htop_identity, ← hmiddle_identity]
    exact (div_div_div_cancel_right₀ hleft_positive.ne' _ _).symm
  rw [hgap_identity, hleft_identity, hright_identity]
  exact ⟨coarse_log_left_bridge_uniform hlower hupper hrelative,
    coarse_log_right_bridge_uniform hlower hupper hrelative hrelative_upper⟩

/-- The derivative bounds for log order every next-generation gap below every
previous-generation gap by the fixed factor ratio/(1-ratio). -/
theorem coarse_log_next_generation_bound
    {ratio firstLeft firstRight nextLeft nextRight : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1)
    (hfirst_lower : 1 - ratio ≤ firstLeft) (hfirst_order : firstLeft ≤ firstRight)
    (hfirst_upper : firstRight ≤ 1)
    (hnext_lower : 1 - ratio ≤ nextLeft) (hnext_order : nextLeft ≤ nextRight)
    (hnext_upper : nextRight ≤ 1)
    (hscale : nextRight - nextLeft ≤ ratio * (firstRight - firstLeft)) :
    Real.log (nextRight / nextLeft) ≤
      ratio / (1 - ratio) * Real.log (firstRight / firstLeft) := by
  have hfirst := coarse_log_interval_bounds hratio hless hfirst_lower hfirst_order hfirst_upper
  have hnext := coarse_log_interval_bounds hratio hless hnext_lower hnext_order hnext_upper
  calc
    _ ≤ (nextRight - nextLeft) / (1 - ratio) := hnext.2
    _ ≤ (ratio * (firstRight - firstLeft)) / (1 - ratio) :=
      div_le_div_of_nonneg_right hscale (by linarith)
    _ = ratio / (1 - ratio) * (firstRight - firstLeft) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfirst.1 (div_nonneg hratio (by linarith))

end LambdaCantor.Last
