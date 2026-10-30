import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.Last

theorem coarse_root_ratio_certificate {ratio : ℝ}
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 ≤ (24522 / 191989 : ℝ) * ratio ^ 0 + (-216511 / 191989 : ℝ) * ratio ^ 1 + (408500 / 191989 : ℝ) * ratio ^ 2 := by
  have hleft : 0 ≤ ratio - (183 / 500 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : (24522 / 191989 : ℝ) * ratio ^ 0 + (-216511 / 191989 : ℝ) * ratio ^ 1 + (408500 / 191989 : ℝ) * ratio ^ 2 = (41255500 / 12863263 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 1 + (68625000 / 12863263 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem coarse_left_child_ratio_certificate {ratio : ℝ}
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 ≤ (4487526 / 85378487 : ℝ) * ratio ^ 0 + (-4487526 / 85378487 : ℝ) * ratio ^ 1 + -1 * ratio ^ 2 + (175244500 / 85378487 : ℝ) * ratio ^ 3 := by
  have hleft : 0 ≤ ratio - (183 / 500 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : (4487526 / 85378487 : ℝ) * ratio ^ 0 + (-4487526 / 85378487 : ℝ) * ratio ^ 1 + -1 * ratio ^ 2 + (175244500 / 85378487 : ℝ) * ratio ^ 3 = (860144560500 / 383264028143 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 2 + (5306128250000 / 383264028143 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 1 + (5232656250000 / 383264028143 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem coarse_right_child_ratio_certificate {ratio : ℝ}
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 ≤ (4487526 / 114383987 : ℝ) * ratio ^ 0 + (-118871513 / 114383987 : ℝ) * ratio ^ 2 + (233255500 / 114383987 : ℝ) * ratio ^ 3 := by
  have hleft : 0 ≤ ratio - (183 / 500 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : (4487526 / 114383987 : ℝ) * ratio ^ 0 + (-118871513 / 114383987 : ℝ) * ratio ^ 2 + (233255500 / 114383987 : ℝ) * ratio ^ 3 = (1680993439500 / 513469717643 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 2 + (7959628250000 / 513469717643 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 1 + (7325718750000 / 513469717643 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem coarse_deep_log_gap_certificate {ratio : ℝ}
    (hlower : (183 / 500 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < (45569 / 2000000 : ℝ) * ratio ^ 0 + (-45569 / 2000000 : ℝ) * ratio ^ 1 + -1 * ratio ^ 3 + 2 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (183 / 500 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : (45569 / 2000000 : ℝ) * ratio ^ 0 + (-45569 / 2000000 : ℝ) * ratio ^ 1 + -1 * ratio ^ 3 + 2 * ratio ^ 4 = (878057 / 8000000000 : ℝ) + (1196139747 / 322417936 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 4 + (109757125 / 80604484 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 3 + (1644163125 / 161208968 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 2 + (3670773625 / 80604484 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 1 + (11282492875 / 322417936 : ℝ) * (ratio - (183 / 500 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

end LambdaCantor.Last
