import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.Last

theorem cubic_low_above_one_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < 2 * ratio ^ 1 + -3 * ratio ^ 2 + 4 * ratio ^ 3 + -5 * ratio ^ 4 + 4 * ratio ^ 5 + -3 * ratio ^ 6 + 2 * ratio ^ 7 + -1 * ratio ^ 8 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 2 * ratio ^ 1 + -3 * ratio ^ 2 + 4 * ratio ^ 3 + -5 * ratio ^ 4 + 4 * ratio ^ 5 + -3 * ratio ^ 6 + 2 * ratio ^ 7 + -1 * ratio ^ 8 = (48805428 / 214358881 : ℝ) + 818819207528448 * (ratio - (4 / 11 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 8 + 6579331513974784 * (ratio - (4 / 11 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 7 + 23127795564806144 * (ratio - (4 / 11 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 6 + 46454687213682688 * (ratio - (4 / 11 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 5 + 58315760966348800 * (ratio - (4 / 11 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 4 + 46849355657381888 * (ratio - (4 / 11 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 3 + 23522463821449024 * (ratio - (4 / 11 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 2 + 6748474918975024 * (ratio - (4 / 11 : ℝ)) ^ 7 * ((3 / 8 : ℝ) - ratio) ^ 1 + 847009743881967 * (ratio - (4 / 11 : ℝ)) ^ 8 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_low_band_lower_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 7 * ratio ^ 3 + -9 * ratio ^ 4 + 9 * ratio ^ 5 + -7 * ratio ^ 6 + 5 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 7 * ratio ^ 3 + -9 * ratio ^ 4 + 9 * ratio ^ 5 + -7 * ratio ^ 6 + 5 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 = (40199349 / 4715895382 : ℝ) + 2697732644929536 * (ratio - (4 / 11 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 9 + 31446205695262720 * (ratio - (4 / 11 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 8 + 154389608046526464 * (ratio - (4 / 11 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 7 + 426843626071130112 * (ratio - (4 / 11 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 6 + 739953187969073152 * (ratio - (4 / 11 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 5 + 839427745103712256 * (ratio - (4 / 11 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 4 + 625793317278010880 * (ratio - (4 / 11 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 3 + 296497354562709824 * (ratio - (4 / 11 : ℝ)) ^ 7 * ((3 / 8 : ℝ) - ratio) ^ 2 + 81184349719701656 * (ratio - (4 / 11 : ℝ)) ^ 8 * ((3 / 8 : ℝ) - ratio) ^ 1 + 9803264225426777 * (ratio - (4 / 11 : ℝ)) ^ 9 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_low_band_upper_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < -1 * ratio ^ 1 + 4 * ratio ^ 2 + -4 * ratio ^ 3 + 3 * ratio ^ 4 + -2 * ratio ^ 5 + 1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 1 + 4 * ratio ^ 2 + -4 * ratio ^ 3 + 3 * ratio ^ 4 + -2 * ratio ^ 5 + 1 * ratio ^ 6 = (13290 / 1771561 : ℝ) + 3483893760 * (ratio - (4 / 11 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 6 + 24927961088 * (ratio - (4 / 11 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 5 + 72460386304 * (ratio - (4 / 11 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 4 + 110238910464 * (ratio - (4 / 11 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 3 + 92975628480 * (ratio - (4 / 11 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 2 + 41339627920 * (ratio - (4 / 11 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 1 + 7586590929 * (ratio - (4 / 11 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_low_lower_corner_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < -1 * ratio ^ 0 + 3 * ratio ^ 1 + -3 * ratio ^ 2 + 10 * ratio ^ 3 + -12 * ratio ^ 4 + 12 * ratio ^ 5 + -10 * ratio ^ 6 + 6 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 3 * ratio ^ 1 + -3 * ratio ^ 2 + 10 * ratio ^ 3 + -12 * ratio ^ 4 + 12 * ratio ^ 5 + -10 * ratio ^ 6 + 6 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 = (53410129 / 4715895382 : ℝ) + 3584293083283456 * (ratio - (4 / 11 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 9 + 43854623089360896 * (ratio - (4 / 11 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 8 + 221891236693278720 * (ratio - (4 / 11 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 7 + 626390569748791296 * (ratio - (4 / 11 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 6 + 1102865397722775552 * (ratio - (4 / 11 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 5 + 1266459038943264768 * (ratio - (4 / 11 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 4 + 953578563263550464 * (ratio - (4 / 11 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 3 + 455597962181917056 * (ratio - (4 / 11 : ℝ)) ^ 7 * ((3 / 8 : ℝ) - ratio) ^ 2 + 125652510337496856 * (ratio - (4 / 11 : ℝ)) ^ 8 * ((3 / 8 : ℝ) - ratio) ^ 1 + 15269807137051033 * (ratio - (4 / 11 : ℝ)) ^ 9 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_low_upper_corner_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < 1 * ratio ^ 0 + -3 * ratio ^ 1 + 3 * ratio ^ 2 + -10 * ratio ^ 3 + 18 * ratio ^ 4 + -18 * ratio ^ 5 + 19 * ratio ^ 6 + -18 * ratio ^ 7 + 15 * ratio ^ 8 + -10 * ratio ^ 9 + 6 * ratio ^ 10 + -3 * ratio ^ 11 + 1 * ratio ^ 12 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 0 + -3 * ratio ^ 1 + 3 * ratio ^ 2 + -10 * ratio ^ 3 + 18 * ratio ^ 4 + -18 * ratio ^ 5 + 19 * ratio ^ 6 + -18 * ratio ^ 7 + 15 * ratio ^ 8 + -10 * ratio ^ 9 + 6 * ratio ^ 10 + -3 * ratio ^ 11 + 1 * ratio ^ 12 = (2112843241 / 137438953472 : ℝ) + (18258314537501606557959 / 2 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 12 + 103706364682055110448682 * (ratio - (4 / 11 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 11 + 538274369787092501486055 * (ratio - (4 / 11 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 10 + 1687309351503728678568194 * (ratio - (4 / 11 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 9 + (7112109732975849707816073 / 2 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 8 + 5305418863947985021581012 * (ratio - (4 / 11 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 7 + 5741762823783212340931234 * (ratio - (4 / 11 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 6 + 4537968293734054456276692 * (ratio - (4 / 11 : ℝ)) ^ 7 * ((3 / 8 : ℝ) - ratio) ^ 5 + (5193493654347500662629513 / 2 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 8 * ((3 / 8 : ℝ) - ratio) ^ 4 + 1047776406886994320966914 * (ratio - (4 / 11 : ℝ)) ^ 9 * ((3 / 8 : ℝ) - ratio) ^ 3 + 282464410947177887455335 * (ratio - (4 / 11 : ℝ)) ^ 10 * ((3 / 8 : ℝ) - ratio) ^ 2 + 45568678284649913829282 * (ratio - (4 / 11 : ℝ)) ^ 11 * ((3 / 8 : ℝ) - ratio) ^ 1 + (6631007183117566592761 / 2 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 12 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_high_above_one_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < 2 * ratio ^ 1 + -3 * ratio ^ 2 + 2 * ratio ^ 3 + -1 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 2 * ratio ^ 1 + -3 * ratio ^ 2 + 2 * ratio ^ 3 + -1 * ratio ^ 4 = (1695 / 8192 : ℝ) + (1695 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 4 + 3586 * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 3 + 5571 * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 2 + 3778 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 1 + (1889 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_high_band_lower_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 5 * ratio ^ 3 + -3 * ratio ^ 4 + 1 * ratio ^ 5 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 5 * ratio ^ 3 + -3 * ratio ^ 4 + 1 * ratio ^ 5 = (283 / 65536 : ℝ) + (283 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 5 + (16369 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 4 + 30617 * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 3 + 44281 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 2 + (57465 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 1 + (14053 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 5 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_high_band_upper_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 1 + 4 * ratio ^ 2 + -4 * ratio ^ 3 + 3 * ratio ^ 4 + -2 * ratio ^ 5 + 1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 1 + 4 * ratio ^ 2 + -4 * ratio ^ 3 + 3 * ratio ^ 4 + -2 * ratio ^ 5 + 1 * ratio ^ 6 = (6249 / 524288 : ℝ) + (6249 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 6 + 44701 * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 5 + (363705 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 4 + 342246 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 3 + (671705 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 2 + 167621 * (ratio - (3 / 8 : ℝ)) ^ 5 * ((1 / 2 : ℝ) - ratio) ^ 1 + (67479 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 6 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_high_lower_corner_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 0 + 3 * ratio ^ 1 + -3 * ratio ^ 2 + 10 * ratio ^ 3 + -12 * ratio ^ 4 + 12 * ratio ^ 5 + -10 * ratio ^ 6 + 6 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 3 * ratio ^ 1 + -3 * ratio ^ 2 + 10 * ratio ^ 3 + -12 * ratio ^ 4 + 12 * ratio ^ 5 + -10 * ratio ^ 6 + 6 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 = (7995979 / 268435456 : ℝ) + (7995979 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 9 + (181833333 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 8 + 588072186 * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 7 + 1907054770 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 6 + 3680309643 * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 5 + 4517836683 * (ratio - (3 / 8 : ℝ)) ^ 5 * ((1 / 2 : ℝ) - ratio) ^ 4 + 3582320562 * (ratio - (3 / 8 : ℝ)) ^ 6 * ((1 / 2 : ℝ) - ratio) ^ 3 + 1784993466 * (ratio - (3 / 8 : ℝ)) ^ 7 * ((1 / 2 : ℝ) - ratio) ^ 2 + (1019997021 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 8 * ((1 / 2 : ℝ) - ratio) ^ 1 + (127794613 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 9 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem cubic_high_upper_corner_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < 1 * ratio ^ 0 + -3 * ratio ^ 1 + 3 * ratio ^ 2 + -4 * ratio ^ 3 + 6 * ratio ^ 4 + -3 * ratio ^ 5 + 1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 0 + -3 * ratio ^ 1 + 3 * ratio ^ 2 + -4 * ratio ^ 3 + 6 * ratio ^ 4 + -3 * ratio ^ 5 + 1 * ratio ^ 6 = (3 / 128 : ℝ) + 42385 * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 6 + 207648 * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 5 + 411792 * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 4 + 419328 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 3 + 228096 * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 2 + 61440 * (ratio - (3 / 8 : ℝ)) ^ 5 * ((1 / 2 : ℝ) - ratio) ^ 1 + 6144 * (ratio - (3 / 8 : ℝ)) ^ 6 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_low_above_complement_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (147 / 400 : ℝ)) :
    0 < 1 * ratio ^ 3 + -1 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (147 / 400 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 3 + -1 * ratio ^ 4 = (224 / 14641 : ℝ) + (5734400000000 / 83521 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((147 / 400 : ℝ) - ratio) ^ 4 + (23233536000000 / 83521 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((147 / 400 : ℝ) - ratio) ^ 3 + (35295872640000 / 83521 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((147 / 400 : ℝ) - ratio) ^ 2 + (23828727454000 / 83521 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((147 / 400 : ℝ) - ratio) ^ 1 + (6031990730479 / 83521 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((147 / 400 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_low_below_one_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (147 / 400 : ℝ)) :
    0 < 1 * ratio ^ 1 + -1 * ratio ^ 3 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (147 / 400 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 1 + -1 * ratio ^ 3 = (210 / 1331 : ℝ) + (13440000000 / 4913 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((147 / 400 : ℝ) - ratio) ^ 3 + (40518560000 / 4913 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((147 / 400 : ℝ) - ratio) ^ 2 + (40715732800 / 4913 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((147 / 400 : ℝ) - ratio) ^ 1 + (13637167887 / 4913 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((147 / 400 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_low_band_lower_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (147 / 400 : ℝ)) :
    0 < -1 * ratio ^ 0 + 3 * ratio ^ 1 + -2 * ratio ^ 3 + 1 * ratio ^ 4 + 1 * ratio ^ 5 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (147 / 400 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 3 * ratio ^ 1 + -2 * ratio ^ 3 + 1 * ratio ^ 4 + 1 * ratio ^ 5 = (2993 / 322102 : ℝ) + (15324160000000000 / 1419857 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((147 / 400 : ℝ) - ratio) ^ 5 + (92463385600000000 / 1419857 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((147 / 400 : ℝ) - ratio) ^ 4 + (216589599232000000 / 1419857 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((147 / 400 : ℝ) - ratio) ^ 3 + (248230157987520000 / 1419857 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((147 / 400 : ℝ) - ratio) ^ 2 + (139924261714700400 / 1419857 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((147 / 400 : ℝ) - ratio) ^ 1 + (31144477360600257 / 1419857 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 5 * ((147 / 400 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_low_lower_corner_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (147 / 400 : ℝ)) :
    0 < -1 * ratio ^ 0 + 4 * ratio ^ 1 + -3 * ratio ^ 2 + -2 * ratio ^ 3 + 6 * ratio ^ 4 + -2 * ratio ^ 5 + -1 * ratio ^ 6 + 2 * ratio ^ 7 + -1 * ratio ^ 8 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (147 / 400 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 4 * ratio ^ 1 + -3 * ratio ^ 2 + -2 * ratio ^ 3 + 6 * ratio ^ 4 + -2 * ratio ^ 5 + -1 * ratio ^ 6 + 2 * ratio ^ 7 + -1 * ratio ^ 8 = (11348383 / 428717762 : ℝ) + (3718638141440000000000000000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((147 / 400 : ℝ) - ratio) ^ 8 + (30830011803238400000000000000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((147 / 400 : ℝ) - ratio) ^ 7 + (111685188289417216000000000000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((147 / 400 : ℝ) - ratio) ^ 6 + (230924650108218675200000000000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((147 / 400 : ℝ) - ratio) ^ 5 + (298091169491332005017600000000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((147 / 400 : ℝ) - ratio) ^ 4 + (246015265478621837119616000000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 5 * ((147 / 400 : ℝ) - ratio) ^ 3 + (126775836136488574767766880000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 6 * ((147 / 400 : ℝ) - ratio) ^ 2 + (37297455506700776605731068000 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 7 * ((147 / 400 : ℝ) - ratio) ^ 1 + (4796550838101893133004430559 / 6975757441 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 8 * ((147 / 400 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_low_upper_corner_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (147 / 400 : ℝ)) :
    0 < 1 * ratio ^ 0 + -4 * ratio ^ 1 + 3 * ratio ^ 2 + 2 * ratio ^ 3 + -2 * ratio ^ 4 + 1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (147 / 400 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 0 + -4 * ratio ^ 1 + 3 * ratio ^ 2 + 2 * ratio ^ 3 + -2 * ratio ^ 4 + 1 * ratio ^ 6 = (1712800449529 / 8192000000000000 : ℝ) + (79090469522831955231 / 48275138 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((147 / 400 : ℝ) - ratio) ^ 6 + (198825492408495865693 / 24137569 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((147 / 400 : ℝ) - ratio) ^ 5 + (802733530522479328465 / 48275138 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((147 / 400 : ℝ) - ratio) ^ 4 + (408116854198559552310 / 24137569 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((147 / 400 : ℝ) - ratio) ^ 3 + (422452747330465888465 / 48275138 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((147 / 400 : ℝ) - ratio) ^ 2 + (46713192319393052893 / 24137569 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 5 * ((147 / 400 : ℝ) - ratio) ^ 1 + (3034330477168044769 / 48275138 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 6 * ((147 / 400 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_middle_above_complement_certificate {ratio : ℝ}
    (hlower : (147 / 400 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < 1 * ratio ^ 2 + -1 * ratio ^ 3 := by
  have hleft : 0 ≤ ratio - (147 / 400 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 2 + -1 * ratio ^ 3 = (5467077 / 128000000 : ℝ) + (607453 / 6 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 3 + (1857541 / 6 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 2 + (1892641 / 6 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 1 + (642547 / 6 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_middle_below_one_certificate {ratio : ℝ}
    (hlower : (147 / 400 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < 1 * ratio ^ 1 + -1 * ratio ^ 2 + 1 * ratio ^ 3 + -1 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (147 / 400 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 1 + -1 * ratio ^ 2 + 1 * ratio ^ 3 + -1 * ratio ^ 4 = (6754220319 / 51200000000 : ℝ) + (2251406773 / 54 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 4 + (1510999418 / 9 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 3 + (2281478227 / 9 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 2 + (4592686454 / 27 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 1 + (770364409 / 18 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_middle_band_lower_certificate {ratio : ℝ}
    (hlower : (147 / 400 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < -1 * ratio ^ 0 + 3 * ratio ^ 1 + -1 * ratio ^ 2 + 1 * ratio ^ 3 + -1 * ratio ^ 4 + 1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (147 / 400 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 3 * ratio ^ 1 + -1 * ratio ^ 2 + 1 * ratio ^ 3 + -1 * ratio ^ 4 + 1 * ratio ^ 6 = (5325549409529 / 8192000000000000 : ℝ) + (5325549409529 / 1458 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 6 + (31046951602571 / 243 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 5 + (283775070537355 / 486 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 4 + (824498272404710 / 729 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 3 + (540657415452355 / 486 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 2 + (133800075590471 / 243 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 1 + (159455700590471 / 1458 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_middle_lower_corner_certificate {ratio : ℝ}
    (hlower : (147 / 400 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 6 * ratio ^ 3 + -3 * ratio ^ 4 + 2 * ratio ^ 5 + -1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (147 / 400 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 6 * ratio ^ 3 + -3 * ratio ^ 4 + 2 * ratio ^ 5 + -1 * ratio ^ 6 = (199640259156071 / 8192000000000000 : ℝ) + (199640259156071 / 1458 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 6 + (24802094400781 / 27 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 5 + (1233972308474645 / 486 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 4 + (2703676653939290 / 729 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 3 + (489898380573215 / 162 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 2 + (317509115843929 / 243 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 1 + (341078490843929 / 1458 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_middle_upper_corner_certificate {ratio : ℝ}
    (hlower : (147 / 400 : ℝ) ≤ ratio) (hupper : ratio ≤ (3 / 8 : ℝ)) :
    0 < 1 * ratio ^ 0 + -4 * ratio ^ 1 + 5 * ratio ^ 2 + -6 * ratio ^ 3 + 7 * ratio ^ 4 + -4 * ratio ^ 5 + 3 * ratio ^ 6 + -2 * ratio ^ 7 + 1 * ratio ^ 8 := by
  have hleft : 0 ≤ ratio - (147 / 400 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (3 / 8 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 0 + -4 * ratio ^ 1 + 5 * ratio ^ 2 + -6 * ratio ^ 3 + 7 * ratio ^ 4 + -4 * ratio ^ 5 + 3 * ratio ^ 6 + -2 * ratio ^ 7 + 1 * ratio ^ 8 = (35761 / 33554432 : ℝ) + (8648874420742461761 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 0 * ((3 / 8 : ℝ) - ratio) ^ 8 + (61141498076919785200 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 1 * ((3 / 8 : ℝ) - ratio) ^ 7 + (185920808728998830000 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 2 * ((3 / 8 : ℝ) - ratio) ^ 6 + (315890626932709000000 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 3 * ((3 / 8 : ℝ) - ratio) ^ 5 + (325172234288637500000 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 4 * ((3 / 8 : ℝ) - ratio) ^ 4 + (204583377272500000000 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 5 * ((3 / 8 : ℝ) - ratio) ^ 3 + (74613840312500000000 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 6 * ((3 / 8 : ℝ) - ratio) ^ 2 + (13438712500000000000 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 7 * ((3 / 8 : ℝ) - ratio) ^ 1 + (698457031250000000 / 6561 : ℝ) * (ratio - (147 / 400 : ℝ)) ^ 8 * ((3 / 8 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_high_above_complement_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < 1 * ratio ^ 2 + -1 * ratio ^ 3 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 2 + -1 * ratio ^ 3 = (45 / 1024 : ℝ) + (45 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 3 + (177 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 2 + (217 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 1 + (83 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_high_below_one_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < 1 * ratio ^ 1 + -1 * ratio ^ 2 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 1 + -1 * ratio ^ 2 = (15 / 128 : ℝ) + (15 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 2 + 17 * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 1 + (17 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_high_band_lower_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 0 + 3 * ratio ^ 1 + -1 * ratio ^ 2 + 1 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 3 * ratio ^ 1 + -1 * ratio ^ 2 + 1 * ratio ^ 4 = (17 / 8192 : ℝ) + (17 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 4 + 1294 * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 3 + 3821 * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 2 + 3806 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 1 + (2543 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_high_lower_corner_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 6 * ratio ^ 3 + -3 * ratio ^ 4 + 2 * ratio ^ 5 + -1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 4 * ratio ^ 1 + -5 * ratio ^ 2 + 6 * ratio ^ 3 + -3 * ratio ^ 4 + 2 * ratio ^ 5 + -1 * ratio ^ 6 = (17303 / 524288 : ℝ) + (17303 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 6 + 127331 * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 5 + (1013575 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 4 + 928538 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 3 + (1776679 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 2 + 433467 * (ratio - (3 / 8 : ℝ)) ^ 5 * ((1 / 2 : ℝ) - ratio) ^ 1 + (171113 / 2 : ℝ) * (ratio - (3 / 8 : ℝ)) ^ 6 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem quadratic_high_upper_corner_certificate {ratio : ℝ}
    (hlower : (3 / 8 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < 1 * ratio ^ 0 + -4 * ratio ^ 1 + 5 * ratio ^ 2 + -2 * ratio ^ 3 + 1 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (3 / 8 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 0 + -4 * ratio ^ 1 + 5 * ratio ^ 2 + -2 * ratio ^ 3 + 1 * ratio ^ 4 = (1 / 32 : ℝ) + 353 * (ratio - (3 / 8 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 4 + 960 * (ratio - (3 / 8 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 3 + 992 * (ratio - (3 / 8 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 2 + 512 * (ratio - (3 / 8 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 1 + 128 * (ratio - (3 / 8 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem three_halves_band_lower_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 0 + 4 * ratio ^ 1 + -4 * ratio ^ 2 + 3 * ratio ^ 3 + -1 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 4 * ratio ^ 1 + -4 * ratio ^ 2 + 3 * ratio ^ 3 + -1 * ratio ^ 4 = (767 / 29282 : ℝ) + (6136 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 4 + (91264 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 3 + (76784 / 27 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 2 + (212374 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 1 + (67069 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem three_halves_band_upper_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 0 + 3 * ratio ^ 1 + -1 * ratio ^ 3 + -2 * ratio ^ 4 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + 3 * ratio ^ 1 + -1 * ratio ^ 3 + -2 * ratio ^ 4 = (115 / 29282 : ℝ) + (920 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 4 + (74552 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 3 + (68824 / 27 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 2 + (190646 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 1 + (57644 / 81 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem three_halves_lower_corner_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < -1 * ratio ^ 0 + (21 / 4 : ℝ) * ratio ^ 1 + (-21 / 2 : ℝ) * ratio ^ 2 + (67 / 4 : ℝ) * ratio ^ 3 + (-33 / 2 : ℝ) * ratio ^ 4 + (57 / 4 : ℝ) * ratio ^ 5 + -10 * ratio ^ 6 + 6 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : -1 * ratio ^ 0 + (21 / 4 : ℝ) * ratio ^ 1 + (-21 / 2 : ℝ) * ratio ^ 2 + (67 / 4 : ℝ) * ratio ^ 3 + (-33 / 2 : ℝ) * ratio ^ 4 + (57 / 4 : ℝ) * ratio ^ 5 + -10 * ratio ^ 6 + 6 * ratio ^ 7 + -3 * ratio ^ 8 + 1 * ratio ^ 9 = (128848001 / 2357947691 : ℝ) + (65970176512 / 19683 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 9 + (103079330752 / 2187 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 8 + (559627056832 / 2187 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 7 + (4945540892656 / 6561 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 6 + (2987625278864 / 2187 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 5 + (3505418592044 / 2187 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 5 * ((1 / 2 : ℝ) - ratio) ^ 4 + (8056399602208 / 6561 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 6 * ((1 / 2 : ℝ) - ratio) ^ 3 + (1302264252880 / 2187 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 7 * ((1 / 2 : ℝ) - ratio) ^ 2 + (364033738774 / 2187 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 8 * ((1 / 2 : ℝ) - ratio) ^ 1 + (403261413997 / 19683 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 9 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem three_halves_upper_corner_certificate {ratio : ℝ}
    (hlower : (4 / 11 : ℝ) ≤ ratio) (hupper : ratio ≤ (1 / 2 : ℝ)) :
    0 < 1 * ratio ^ 0 + (-21 / 4 : ℝ) * ratio ^ 1 + (21 / 2 : ℝ) * ratio ^ 2 + (-37 / 4 : ℝ) * ratio ^ 3 + 6 * ratio ^ 4 + -3 * ratio ^ 5 + 1 * ratio ^ 6 := by
  have hleft : 0 ≤ ratio - (4 / 11 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (1 / 2 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : 1 * ratio ^ 0 + (-21 / 4 : ℝ) * ratio ^ 1 + (21 / 2 : ℝ) * ratio ^ 2 + (-37 / 4 : ℝ) * ratio ^ 3 + 6 * ratio ^ 4 + -3 * ratio ^ 5 + 1 * ratio ^ 6 = (32679 / 585640 : ℝ) + (1404824 / 135 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 0 * ((1 / 2 : ℝ) - ratio) ^ 6 + (7417784 / 135 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 1 * ((1 / 2 : ℝ) - ratio) ^ 5 + (3514808 / 27 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 2 * ((1 / 2 : ℝ) - ratio) ^ 4 + (1601798 / 9 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 3 * ((1 / 2 : ℝ) - ratio) ^ 3 + (3952102 / 27 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 4 * ((1 / 2 : ℝ) - ratio) ^ 2 + (9075484 / 135 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 5 * ((1 / 2 : ℝ) - ratio) ^ 1 + (1780999 / 135 : ℝ) * (ratio - (4 / 11 : ℝ)) ^ 6 * ((1 / 2 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

end LambdaCantor.Last
