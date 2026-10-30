import LambdaCantor.Last.AnalyticCoarseSecantCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
namespace LambdaCantor.Last

def coarseSecantError (scale : ℝ) : ℝ :=
  scale ^ 2 * (503 / 500) ^ 2 / (160 * (1 - scale * (503 / 500) / 20) ^ 2)

theorem coarse_secant_denominator_positive {scale : ℝ} (hupper : scale ≤ 11 / 4) :
    0 < 160 * (1 - scale * (503 / 500) / 20) ^ 2 := by
  have : 0 < 1 - scale * (503 / 500) / 20 := by linarith
  positivity

theorem coarse_secant_first_comparison {scale : ℝ}
    (hlower : 1 ≤ scale) (hupper : scale ≤ 500 / 317) :
    (503 / 500) * (scale * (67 / 250)) + coarseSecantError scale < 91 / 200 := by
  have hden := coarse_secant_denominator_positive (show scale ≤ 11 / 4 by linarith)
  suffices coarseSecantError scale < 91 / 200 - (503 / 500) * (scale * (67 / 250)) by linarith
  rw [coarseSecantError]
  apply (div_lt_iff₀ hden).mpr
  nlinarith [coarse_secant_first_certificate hlower hupper]

theorem coarse_secant_middle_comparison {scale : ℝ}
    (hlower : 500 / 317 ≤ scale) (hupper : scale ≤ 433 / 250) :
    (503 / 500) * (2 - scale) + coarseSecantError scale < 91 / 200 := by
  have hden := coarse_secant_denominator_positive (show scale ≤ 11 / 4 by linarith)
  suffices coarseSecantError scale < 91 / 200 - (503 / 500) * (2 - scale) by linarith
  rw [coarseSecantError]
  apply (div_lt_iff₀ hden).mpr
  nlinarith [coarse_secant_middle_certificate hlower hupper]

theorem coarse_secant_last_comparison {scale : ℝ}
    (hlower : 433 / 250 ≤ scale) (hupper : scale ≤ 11 / 4) :
    (503 / 500) * (67 / 250) + coarseSecantError scale < 91 / 200 := by
  have hden := coarse_secant_denominator_positive hupper
  suffices coarseSecantError scale < 91 / 200 - (503 / 500) * (67 / 250) by linarith
  rw [coarseSecantError]
  apply (div_lt_iff₀ hden).mpr
  nlinarith [coarse_secant_last_certificate hlower hupper]

/-- Uniform final arithmetic comparison for the actual three-piece circle
bound. Every polynomial sign is proved by an exact rational identity. -/
theorem coarse_circle_secant_total_lt {ratio scale : ℝ}
    (hratio : 183 / 500 ≤ ratio) (hlower : 1 ≤ scale) (hupper : scale ≤ 11 / 4) :
    (503 / 500) * max (1 - 2 * ratio) (min (scale * (1 - 2 * ratio)) (2 - scale)) +
      coarseSecantError scale < 91 / 200 := by
  have hbase : 1 - 2 * ratio ≤ (67 / 250 : ℝ) := by linarith
  have hgap : max (1 - 2 * ratio) (min (scale * (1 - 2 * ratio)) (2 - scale)) ≤
      max (67 / 250 : ℝ) (min (scale * (67 / 250)) (2 - scale)) :=
    max_le_max hbase (min_le_min
      (mul_le_mul_of_nonneg_left hbase (by linarith)) (le_refl _))
  have hfixed : (503 / 500) *
      max (67 / 250 : ℝ) (min (scale * (67 / 250)) (2 - scale)) +
        coarseSecantError scale < 91 / 200 := by
    by_cases hfirst : scale ≤ 500 / 317
    · have hmin : scale * (67 / 250 : ℝ) ≤ 2 - scale := by linarith
      have hmax : (67 / 250 : ℝ) ≤ scale * (67 / 250) := by linarith
      rw [min_eq_left hmin, max_eq_right hmax]
      exact coarse_secant_first_comparison hlower hfirst
    · by_cases hmiddle : scale ≤ 433 / 250
      · have hmin : 2 - scale ≤ scale * (67 / 250 : ℝ) := by linarith
        have hmax : (67 / 250 : ℝ) ≤ 2 - scale := by linarith
        rw [min_eq_right hmin, max_eq_right hmax]
        exact coarse_secant_middle_comparison (by linarith) hmiddle
      · have hmax : min (scale * (67 / 250 : ℝ)) (2 - scale) ≤ 67 / 250 :=
          (min_le_right _ _).trans (by linarith)
        rw [max_eq_left hmax]
        exact coarse_secant_last_comparison (by linarith) hupper
  exact (add_le_add (mul_le_mul_of_nonneg_left hgap (by norm_num))
    (le_refl (coarseSecantError scale))).trans_lt hfixed

end LambdaCantor.Last
