import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.Last

theorem coarse_secant_first_certificate {ratio : ℝ}
    (hlower : 1 ≤ ratio) (hupper : ratio ≤ (500 / 317 : ℝ)) :
    0 < (364 / 5 : ℝ) * ratio ^ 0 + (-315381 / 6250 : ℝ) * ratio ^ 1 + (87794123 / 25000000 : ℝ) * ratio ^ 2 + (-8526656309 / 78125000000 : ℝ) * ratio ^ 3 := by
  have hleft : 0 ≤ ratio - 1 := sub_nonneg.mpr hlower
  have hright : 0 ≤ (500 / 317 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : (364 / 5 : ℝ) * ratio ^ 0 + (-315381 / 6250 : ℝ) * ratio ^ 1 + (87794123 / 25000000 : ℝ) * ratio ^ 2 + (-8526656309 / 78125000000 : ℝ) * ratio ^ 3 = (120809903739 / 159275065000 : ℝ) + (3454162550652653881 / 26599335937500000 : ℝ) * (ratio - 1) ^ 0 * ((500 / 317 : ℝ) - ratio) ^ 3 + (329729988686047921 / 1276768125000000 : ℝ) * (ratio - 1) ^ 1 * ((500 / 317 : ℝ) - ratio) ^ 2 + (84551640125047 / 638384062500 : ℝ) * (ratio - 1) ^ 2 * ((500 / 317 : ℝ) - ratio) ^ 1 + (40269967913 / 10214145000 : ℝ) * (ratio - 1) ^ 3 * ((500 / 317 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem coarse_secant_middle_certificate {ratio : ℝ}
    (hlower : (500 / 317 : ℝ) ≤ ratio) (hupper : ratio ≤ (433 / 250 : ℝ)) :
    0 < (-6228 / 25 : ℝ) * ratio ^ 0 + (5813171 / 31250 : ℝ) * ratio ^ 1 + (-11146817513 / 625000000 : ℝ) * ratio ^ 2 + (127263527 / 312500000 : ℝ) * ratio ^ 3 := by
  have hleft : 0 ≤ ratio - (500 / 317 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (433 / 250 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : (-6228 / 25 : ℝ) * ratio ^ 0 + (5813171 / 31250 : ℝ) * ratio ^ 1 + (-11146817513 / 625000000 : ℝ) * ratio ^ 2 + (127263527 / 312500000 : ℝ) * ratio ^ 3 = (120809903739 / 159275065000 : ℝ) + (125843649728125 / 614407378527 : ℝ) * (ratio - (500 / 317 : ℝ)) ^ 0 * ((433 / 250 : ℝ) - ratio) ^ 3 + (12621044351879761 / 2048024595090 : ℝ) * (ratio - (500 / 317 : ℝ)) ^ 1 * ((433 / 250 : ℝ) - ratio) ^ 2 + (1981089189497470251217 / 170668716257500000 : ℝ) * (ratio - (500 / 317 : ℝ)) ^ 2 * ((433 / 250 : ℝ) - ratio) ^ 1 + (542453381192985835726927 / 96001152894843750000 : ℝ) * (ratio - (500 / 317 : ℝ)) ^ 3 * ((433 / 250 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

theorem coarse_secant_last_certificate {ratio : ℝ}
    (hlower : (433 / 250 : ℝ) ≤ ratio) (hupper : ratio ≤ (11 / 4 : ℝ)) :
    0 < (92696 / 3125 : ℝ) * ratio ^ 0 + (-5828261 / 1953125 : ℝ) * ratio ^ 1 + (-36601040967 / 39062500000 : ℝ) * ratio ^ 2 := by
  have hleft : 0 ≤ ratio - (433 / 250 : ℝ) := sub_nonneg.mpr hlower
  have hright : 0 ≤ (11 / 4 : ℝ) - ratio := sub_nonneg.mpr hupper
  have hidentity : (92696 / 3125 : ℝ) * ratio ^ 0 + (-5828261 / 1953125 : ℝ) * ratio ^ 1 + (-36601040967 / 39062500000 : ℝ) * ratio ^ 2 = (8981604362993 / 1250000000000 : ℝ) + (283168610749339471 / 20240703125000000 : ℝ) * (ratio - (433 / 250 : ℝ)) ^ 0 * ((11 / 4 : ℝ) - ratio) ^ 2 + (1769885790042591 / 80962812500000 : ℝ) * (ratio - (433 / 250 : ℝ)) ^ 1 * ((11 / 4 : ℝ) - ratio) ^ 1 + (8981604362993 / 1295405000000 : ℝ) * (ratio - (433 / 250 : ℝ)) ^ 2 * ((11 / 4 : ℝ) - ratio) ^ 0 := by ring
  rw [hidentity]
  positivity

end LambdaCantor.Last
