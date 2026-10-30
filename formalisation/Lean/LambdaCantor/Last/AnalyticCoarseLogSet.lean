import LambdaCantor.Last.OuterQuotient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

noncomputable section
namespace LambdaCantor.Last

/-- The actual logarithmic outer Cantor set, not an interval approximation. -/
def coarseOuterLogSet (ratio : ℝ) : Set ℝ := Real.log '' outerCantor ratio

def CoarseStrictLogLink (ratio exponent : ℝ) : Prop :=
  ∃ shift : ℤ, ∃ value ∈ coarseOuterLogSet ratio,
    exponent * value ∈ Set.Ioo
      (Real.log exponent - shift * (-Real.log ratio) + Real.log (1 - ratio))
      (Real.log exponent - shift * (-Real.log ratio))

theorem zero_mem_coarseOuterLogSet {ratio : ℝ} (hratio : 0 ≤ ratio) (hless : ratio < 1) :
    0 ∈ coarseOuterLogSet ratio := by
  exact ⟨1, one_mem_outerCantor hratio hless, Real.log_one⟩

theorem lower_mem_coarseOuterLogSet (ratio : ℝ) :
    Real.log (1 - ratio) ∈ coarseOuterLogSet ratio :=
  ⟨1 - ratio, lower_mem_outerCantor ratio, rfl⟩

theorem coarseOuterLogSet_bounds {ratio value : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1)
    (hvalue : value ∈ coarseOuterLogSet ratio) :
    value ∈ Set.Icc (Real.log (1 - ratio)) 0 := by
  rcases hvalue with ⟨point, hpoint, rfl⟩
  have hbounds := outerCantor_bounds hratio hless hpoint
  have hone : 0 < 1 - ratio := by linarith
  have hpositive : 0 < point := hone.trans_le hbounds.1
  constructor
  · exact Real.strictMonoOn_log.monotoneOn hone hpositive hbounds.1
  · simpa only [Real.log_one] using
      Real.strictMonoOn_log.monotoneOn hpositive (by norm_num : (0 : ℝ) < 1) hbounds.2

theorem coarse_strict_log_link_of_small_exponent {ratio exponent : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1)
    (hexponent : 1 < exponent) (hproduct : exponent * (1 - ratio) < 1) :
    CoarseStrictLogLink ratio exponent := by
  have hpositive : 0 < exponent := by linarith
  have hone : 0 < 1 - ratio := by linarith
  have hlog_positive : 0 < Real.log exponent := Real.log_pos hexponent
  have hlog_product := Real.log_neg (mul_pos hpositive hone) hproduct
  rw [Real.log_mul hpositive.ne' hone.ne'] at hlog_product
  refine ⟨0, 0, zero_mem_coarseOuterLogSet hratio hless, ?_⟩
  simp only [Int.cast_zero, zero_mul, sub_zero, mul_zero, Set.mem_Ioo]
  exact ⟨by linarith, hlog_positive⟩

theorem coarse_strict_log_link_first_range {ratio exponent : ℝ}
    (hlower : 183 / 500 ≤ ratio) (hupper : ratio < 1 / 2)
    (hexponent : 1 < exponent) (hexponent_upper : exponent ≤ 23 / 19) :
    CoarseStrictLogLink ratio exponent := by
  have hratio : 0 ≤ ratio := by linarith
  have hone : 0 ≤ 1 - ratio := by linarith
  apply coarse_strict_log_link_of_small_exponent hratio (by linarith) hexponent
  have hbound := mul_le_mul_of_nonneg_right hexponent_upper hone
  nlinarith

end LambdaCantor.Last
