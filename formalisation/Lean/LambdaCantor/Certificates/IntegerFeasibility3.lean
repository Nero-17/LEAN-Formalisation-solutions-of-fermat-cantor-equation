import LambdaCantor.Certificates.IntegerGraph3
import LambdaCantor.Integer.Feasibility

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace LambdaCantor.Integer.Band3
def witnessCode (e : Fin 1024) : ℕ := ([0, 0, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 22, 22, 14, 14, 0, 23, 19, 0, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 0, 23, 19, 0, 22, 22, 14, 14, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 0, 0, 20, 20, 20, 15, 15, 15, 15, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 0, 0, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 22, 22, 14, 14, 0, 23, 19, 0, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 20, 20, 15, 15, 15, 15, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 0, 23, 19, 0, 22, 22, 14, 14, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 0, 0, 20, 20, 20, 15, 15, 15, 15, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 0, 0, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 22, 22, 14, 14, 0, 23, 19, 0, 0, 21, 16, 16, 16, 16, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8, 8, 9, 0, 0, 23, 19, 0, 22, 22, 14, 14, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 0, 0] : List ℕ).getD e.val 0
def witnessLower (e : Fin 1024) : Fin 5 := ⟨witnessCode e / 5 % 5, Nat.mod_lt _ (by decide)⟩
def witnessUpper (e : Fin 1024) : Fin 5 := ⟨witnessCode e % 5, Nat.mod_lt _ (by decide)⟩
def excluded (e : Fin 1024) : Prop :=
  let a := (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1
  let b := (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2
  0 ≤ a * 143 + b * 61 ∧ 0 ≤ a * 237 + b * 101 ∧
  (0 < a * 143 + b * 61 ∨ 0 < a * 237 + b * 101)
instance (e : Fin 1024) : Decidable (excluded e) := by unfold excluded; infer_instance
theorem feasibility_check : ∀ e : Fin 1024, e.val ∈ edges ∨ excluded e := by decide +kernel
theorem feasible_mem_edges (e : Fin 1024) (r : ℝ) (hl : (143 : ℝ) / 61 < r) (hu : r < (237 : ℝ) / 101) (h : Feasible e.val r) : e.val ∈ edges := by
  rcases feasibility_check e with hedge | hex
  · exact hedge
  · exfalso
    rcases hex with ⟨hleft, hright, hstrict⟩
    have hleftR : (0 : ℝ) ≤ (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 143 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 61 := by exact_mod_cast hleft
    have hrightR : (0 : ℝ) ≤ (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 237 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 101 := by exact_mod_cast hright
    have positive := positive_inside_band
      ((discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 : ℝ)
      ((discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 : ℝ)
      (143/61) (237/101) r hl hu (by nlinarith) (by nlinarith) (by
        rcases hstrict with hstrict | hstrict
        · left; have hs : (0 : ℝ) < (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 143 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 61 := by exact_mod_cast hstrict
          nlinarith
        · right; have hs : (0 : ℝ) < (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 237 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 101 := by exact_mod_cast hstrict
          nlinarith)
    exact (not_lt_of_ge (h (witnessLower e) (witnessUpper e))) positive
end LambdaCantor.Integer.Band3
