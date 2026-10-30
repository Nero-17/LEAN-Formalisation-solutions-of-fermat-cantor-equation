import LambdaCantor.First.Dimension
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
namespace LambdaCantor.First

open Filter Topology

/-- Rounding a real child-count estimate up to an integer costs only an
additional decaying term. A large fixed block absorbs every finite constant. -/
theorem exists_block_with_rounded_cost {constant growth contraction : ℝ}
    (hconstant : 0 ≤ constant) (hgrowth : 0 ≤ growth)
    (hcontraction : 0 < contraction) (hsmall : contraction < 1)
    (hcost : growth * contraction < 1) :
    ∃ block : ℕ, 0 < block ∧
      (Nat.ceil (constant * growth ^ block) : ℝ) * contraction ^ block < 1 := by
  have hlimit : Tendsto
      (fun block : ℕ => constant * (growth * contraction) ^ block + contraction ^ block)
      atTop (𝓝 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (mul_nonneg hgrowth hcontraction.le) hcost).const_mul constant).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hcontraction.le hsmall)
  have heventual := (tendsto_order.1 hlimit).2 1 zero_lt_one
  obtain ⟨block, hbound, hpositive⟩ := (heventual.and (eventually_gt_atTop 0)).exists
  refine ⟨block, hpositive, ?_⟩
  calc
    _ < (constant * growth ^ block + 1) * contraction ^ block :=
      mul_lt_mul_of_pos_right
        (Nat.ceil_lt_add_one (mul_nonneg hconstant (pow_nonneg hgrowth block)))
        (pow_pos hcontraction block)
    _ = constant * (growth * contraction) ^ block + contraction ^ block := by
      rw [mul_pow]
      ring
    _ < 1 := hbound

theorem exists_projection_block {constant ratio projectionExponent targetExponent : ℝ}
    (hconstant : 0 ≤ constant) (hratio : 0 < ratio) (hcontract : ratio < 1)
    (htarget : 0 < targetExponent)
    (hcost : 4 * ratio ^ (projectionExponent + targetExponent) < 1) :
    ∃ block : ℕ, 0 < block ∧
      (Nat.ceil (constant * (4 * ratio ^ projectionExponent) ^ block) : ℝ) *
        (ratio ^ targetExponent) ^ block < 1 := by
  apply exists_block_with_rounded_cost hconstant
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hratio.le _))
    (Real.rpow_pos_of_pos hratio _) (Real.rpow_lt_one hratio.le hcontract htarget)
  rw [mul_assoc, ← Real.rpow_add hratio]
  exact hcost

end LambdaCantor.First
