import LambdaCantor.Basic
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor

theorem address_half_eq_ofDigits (digits : ℕ → Fin 2) :
    address (1 / 2) (fun j => decide (digits j = 1)) = Real.ofDigits digits := by
  unfold address Real.ofDigits Real.ofDigitsTerm
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  have digit_bound := (digits j).isLt
  have digit_cases : digits j = 0 ∨ digits j = 1 := by omega
  rcases digit_cases with digit_zero | digit_one
  · simp [digit_zero]
  · simp [digit_one, pow_succ, one_div, inv_pow]
    ring

theorem cantorSet_half_eq : cantorSet (1 / 2) = Set.Icc 0 1 := by
  apply Set.Subset.antisymm (cantorSet_subset_unitInterval (by norm_num) (by norm_num))
  intro x membership
  by_cases endpoint : x = 1
  · subst x
    exact one_mem_cantorSet (by norm_num) (by norm_num)
  · refine ⟨fun j => decide (Real.digits x 2 j = 1), ?_⟩
    rw [address_half_eq_ofDigits]
    exact Real.ofDigits_digits (by norm_num) ⟨membership.1, lt_of_le_of_ne membership.2 endpoint⟩

theorem first_projection_intersection_half {exponent : ℝ} (positive : 0 < exponent) :
    Prod.fst '' intersection exponent (1 / 2) = Set.Icc 0 1 := by
  apply Set.Subset.antisymm
  · rintro x ⟨point, membership, rfl⟩
    rw [← cantorSet_half_eq]
    exact membership.1
  · intro x membership
    have power_nonnegative : 0 ≤ x ^ exponent := Real.rpow_nonneg membership.1 _
    have power_le_one : x ^ exponent ≤ 1 := Real.rpow_le_one membership.1 membership.2 positive.le
    refine ⟨(x, (1 - x ^ exponent) ^ exponent⁻¹), ?_, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rwa [cantorSet_half_eq]
    · rw [cantorSet_half_eq]
      exact ⟨Real.rpow_nonneg (by linarith) _,
        Real.rpow_le_one (by linarith) (by linarith) (inv_nonneg.mpr positive.le)⟩
    · dsimp
      rw [Real.rpow_inv_rpow (by linarith) (ne_of_gt positive)]
      ring

theorem one_le_dimH_intersection_half {exponent : ℝ} (positive : 0 < exponent) :
    1 ≤ dimH (intersection exponent (1 / 2)) := by
  have interval_dimension : dimH (Set.Icc (0 : ℝ) 1) = 1 := by
    have interior_nonempty : (interior (Set.Icc (0 : ℝ) 1)).Nonempty := by
      rw [interior_Icc]
      exact ⟨1 / 2, by norm_num⟩
    simpa using Real.dimH_of_nonempty_interior interior_nonempty
  have bound := (LipschitzWith.prod_fst (α := ℝ) (β := ℝ)).dimH_image_le
    (intersection exponent (1 / 2))
  rwa [first_projection_intersection_half positive, interval_dimension] at bound

theorem positive_dimH_intersection_half {exponent : ℝ} (positive : 0 < exponent) :
    0 < dimH (intersection exponent (1 / 2)) :=
  lt_of_lt_of_le (by norm_num) (one_le_dimH_intersection_half positive)

end LambdaCantor
