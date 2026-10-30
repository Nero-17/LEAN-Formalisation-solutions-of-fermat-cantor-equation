import LambdaCantor.Common
import Mathlib.Data.Rat.Floor
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter Topology
namespace LambdaCantor.First

/-- The next rational lattice point is strictly above the target and at most
one lattice step away. This is the floor step in Theorem 2.7. -/
theorem next_lattice_point (target : ℝ) (denominator : ℕ)
    (hdenominator : 0 < denominator) :
    0 < ((⌊(denominator : ℝ) * target⌋ : ℝ) + 1) / denominator - target ∧
    ((⌊(denominator : ℝ) * target⌋ : ℝ) + 1) / denominator - target ≤
      1 / denominator := by
  have hpos : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
  constructor
  · apply sub_pos.mpr
    apply (lt_div_iff₀ hpos).mpr
    simpa [mul_comm] using Int.lt_floor_add_one ((denominator : ℝ) * target)
  · have hfloor := Int.floor_le ((denominator : ℝ) * target)
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hpos).mpr
    rw [add_mul, one_div_mul_cancel (ne_of_gt hpos)]
    nlinarith

/-- Exact cancellation of the limiting residual for powers of four. -/
theorem powers_four_cancellation (r : ℕ) :
    (4 : ℝ) ^ r * (1 / 4 : ℝ) ^ r = 1 := by
  rw [← mul_pow]
  norm_num

/-- The finite-cylinder phase relation used in Proposition 2.9. -/
theorem powers_four_phase (r k : ℕ) :
    (((4 ^ r * k + r : ℕ) : ℝ) - (4 : ℝ) ^ r * k) = r := by
  push_cast
  ring

/-- Infimum conclusion once the geometric construction supplies positive
Hausdorff dimension arbitrarily near one quarter from above. -/
theorem first_eq_quarter_of_parameters (exponent : ℝ)
    (hlower : 1 / 4 ≤ firstTransition exponent)
    (hparameters : ∀ c : ℝ, 1 / 4 < c → c < 1 / 2 →
      ∃ ratio : ℝ, 1 / 4 < ratio ∧ ratio < c ∧
        0 < dimH (intersection exponent ratio)) :
    firstTransition exponent = 1 / 4 := by
  apply le_antisymm _ hlower
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  obtain ⟨ratio, hratio, hrc, hdim⟩ :=
    hparameters (min c (3 / 8)) (lt_min hc (by norm_num))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
  have hmem : ratio ∈ {ratio | ratio ∈ Ioc (0 : ℝ) (1 / 2) ∧
      0 < dimH (intersection exponent ratio)} :=
    ⟨⟨by linarith, by have := min_le_right c (3 / 8 : ℝ); linarith⟩, hdim⟩
  have hbdd : BddBelow {ratio | ratio ∈ Ioc (0 : ℝ) (1 / 2) ∧
      0 < dimH (intersection exponent ratio)} := ⟨0, fun _ h => h.1.1.le⟩
  exact le_trans (csInf_le hbdd hmem) (le_trans hrc.le (min_le_left _ _))

end LambdaCantor.First

