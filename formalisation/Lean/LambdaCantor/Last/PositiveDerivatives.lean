import LambdaCantor.Last.ReturnWords
import LambdaCantor.Last.GeometricScale

noncomputable section
namespace LambdaCantor.Last

def positiveLinear (slope : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun point := point.1 + slope * point.2
  map_add' first second := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' scalar point := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

def positiveLinearContinuous (slope : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ where
  toLinearMap := positiveLinear slope
  cont := continuous_fst.add (continuous_const.mul continuous_snd)

/-- The three strict inequalities in the linear slope criterion. -/
def StrictSlopeConditions (ratio slope : ℝ) : Prop :=
  1 < slope ∧ 1 - ratio - ratio ^ 2 < ratio * slope ∧ (1 - 2 * ratio) * slope < ratio

theorem strictSlopeConditions_iff {ratio slope : ℝ} (hpositive : 0 < ratio)
    (hhalf : ratio < 1 / 2) :
    StrictSlopeConditions ratio slope ↔
      1 < slope ∧ (1 - ratio - ratio ^ 2) / ratio < slope ∧ slope < ratio / (1 - 2 * ratio) := by
  unfold StrictSlopeConditions
  rw [div_lt_iff₀ hpositive, lt_div_iff₀ (show 0 < 1 - 2 * ratio by linarith)]
  constructor <;> rintro ⟨hfirst, hsecond, hthird⟩ <;>
    exact ⟨hfirst, by nlinarith, by nlinarith⟩

theorem strictSlopeConditions_of_derivative_bounds
    {ratio lowerS upperS lowerT upperT derivativeS derivativeT : ℝ}
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hS : lowerS ≤ derivativeS) (hSupper : derivativeS ≤ upperS)
    (hT : lowerT ≤ derivativeT) (hTupper : derivativeT ≤ upperT)
    (hfirst : upperS < lowerT)
    (hsecond : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hthird : (1 - 2 * ratio) * upperT < ratio * lowerS) :
    StrictSlopeConditions ratio (derivativeT / derivativeS) := by
  have hSpositive : 0 < derivativeS := hlowerS.trans_le hS
  have hTpositive : 0 < derivativeT := by linarith
  have hmiddle : (1 - ratio - ratio ^ 2) * derivativeS < ratio * derivativeT := by
    by_cases hcoefficient : 0 ≤ 1 - ratio - ratio ^ 2
    · exact (mul_le_mul_of_nonneg_left hSupper hcoefficient).trans_lt
        (hsecond.trans_le (mul_le_mul_of_nonneg_left hT hratio.le))
    · have hneg : (1 - ratio - ratio ^ 2) * derivativeS < 0 :=
        mul_neg_of_neg_of_pos (lt_of_not_ge hcoefficient) hSpositive
      exact hneg.trans (mul_pos hratio hTpositive)
  have hlast : (1 - 2 * ratio) * derivativeT < ratio * derivativeS :=
    (mul_le_mul_of_nonneg_left hTupper (by linarith)).trans_lt
      (hthird.trans_le (mul_le_mul_of_nonneg_left hS hratio.le))
  unfold StrictSlopeConditions
  refine ⟨(one_lt_div hSpositive).mpr (by linarith), ?_, ?_⟩
  · rw [← mul_div_assoc, lt_div_iff₀ hSpositive]
    exact hmiddle
  · rw [← mul_div_assoc, div_lt_iff₀ hSpositive]
    exact hlast

/-- Overlapping geometric shells cover the whole lower interior interval. -/
theorem geometric_shell_entry {ratio lower upper level : ℝ}
    (hratio : 0 < ratio) (hratio_one : ratio < 1)
    (hlower : 0 < lower) (hoverlap : lower < ratio * upper)
    (hlevel : 0 < level) (hupper : level < upper) :
    ∃ depth : ℕ, lower < level / ratio ^ depth ∧ level / ratio ^ depth < upper := by
  by_cases hlower_level : lower < level
  · exact ⟨0, by simpa using hlower_level, by simpa using hupper⟩
  · obtain ⟨depth, hnext, hcurrent⟩ := exists_nat_pow_near_of_lt_one
      (div_pos hlevel hlower) ((div_le_one hlower).mpr (le_of_not_gt hlower_level))
      hratio hratio_one
    refine ⟨depth + 1, ?_, ?_⟩
    · rw [lt_div_iff₀ (pow_pos hratio _)]
      have := (lt_div_iff₀ hlower).mp hnext
      nlinarith
    · rw [div_lt_iff₀ (pow_pos hratio _)]
      have hcurrent' := (div_le_iff₀ hlower).mp hcurrent
      have hoverlap' := mul_lt_mul_of_pos_right hoverlap (pow_pos hratio depth)
      rw [pow_succ]
      nlinarith

end LambdaCantor.Last
