import LambdaCantor.Basic
import LambdaCantor.Library.CantorSet
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor

theorem address_third_eq_ofDigits (digits : ℕ → Bool) :
    address (1 / 3) digits =
      Real.ofDigits (fun j => cond (digits j) (2 : Fin 3) 0) := by
  unfold address Real.ofDigits Real.ofDigitsTerm
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  cases digit_value : digits j <;>
    simp [digit_value, pow_succ, one_div, mul_inv, inv_pow] <;> ring

theorem cantorSet_third_eq : cantorSet (1 / 3) = _root_.cantorSet := by
  ext x
  constructor
  · rintro ⟨digits, rfl⟩
    rw [address_third_eq_ofDigits]
    exact ofDigits_bool_to_fin_three_mem_cantorSet digits
  · intro membership
    refine ⟨cantorSetEquivNatToBool ⟨x, membership⟩, ?_⟩
    rw [address_third_eq_ofDigits]
    exact congrArg Subtype.val (cantorSetEquivNatToBool.symm_apply_apply ⟨x, membership⟩)

end LambdaCantor
