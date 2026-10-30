import LambdaCantor.Common
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace LambdaCantor.First.LinearRegularity

/-- Pulling back a zero-dimensional exceptional contraction set under any
positive integer power preserves dimension zero on positive parameters. -/
theorem dimH_positive_power_preimage (exceptional : Set ℝ) (hexceptional : dimH exceptional = 0)
    (power : ℕ) (hpower : 0 < power) :
    dimH {ratio : ℝ | 0 < ratio ∧ ratio ^ power ∈ exceptional} = 0 := by
  have hsmooth : ContDiffOn ℝ 1 (fun point : ℝ => point ^ ((power : ℝ)⁻¹)) (Set.Ioi (0 : ℝ)) := by
    intro point hpoint
    exact (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hpoint)).contDiffWithinAt
  have hsubset : {ratio : ℝ | 0 < ratio ∧ ratio ^ power ∈ exceptional} ⊆
      (fun point : ℝ => point ^ ((power : ℝ)⁻¹)) '' (exceptional ∩ Set.Ioi (0 : ℝ)) := by
    intro ratio hratio
    refine ⟨ratio ^ power, ⟨hratio.2, pow_pos hratio.1 _⟩, ?_⟩
    exact Real.pow_rpow_inv_natCast hratio.1.le (Nat.ne_of_gt hpower)
  apply le_antisymm _ bot_le
  calc
    _ ≤ dimH ((fun point : ℝ => point ^ ((power : ℝ)⁻¹)) ''
        (exceptional ∩ Set.Ioi (0 : ℝ))) := dimH_mono hsubset
    _ ≤ dimH (exceptional ∩ Set.Ioi (0 : ℝ)) :=
      hsmooth.dimH_image_le (convex_Ioi (0 : ℝ)) Set.inter_subset_right
    _ ≤ dimH exceptional := dimH_mono Set.inter_subset_left
    _ = 0 := hexceptional

/-- One exceptional set removes every positive integer block contraction
simultaneously, without increasing its Hausdorff dimension. -/
theorem dimH_all_positive_power_preimages (exceptional : Set ℝ)
    (hexceptional : dimH exceptional = 0) :
    dimH (⋃ power : {power : ℕ // 0 < power},
      {ratio : ℝ | 0 < ratio ∧ ratio ^ (power : ℕ) ∈ exceptional}) = 0 := by
  apply le_antisymm _ bot_le
  rw [dimH_iUnion]
  exact iSup_le (fun power => le_of_eq
    (dimH_positive_power_preimage exceptional hexceptional power.val power.property))

end LambdaCantor.First.LinearRegularity

