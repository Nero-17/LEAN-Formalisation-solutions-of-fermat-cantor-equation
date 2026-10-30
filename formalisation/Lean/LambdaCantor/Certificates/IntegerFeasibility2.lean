import LambdaCantor.Certificates.IntegerGraph2
import LambdaCantor.Integer.Feasibility

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace LambdaCantor.Integer.Band2
def witnessCode (e : Fin 1024) : ℕ := ([0, 0, 0, 0, 0, 0, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 21, 21, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 21, 21, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 21, 21, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 0, 0, 0, 22, 22, 14, 14, 0, 20, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 0, 22, 22, 14, 14, 0, 0, 0, 21, 21, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 21, 21, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 20, 20, 15, 15, 15, 15, 15, 15, 15, 15, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 21, 21, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 21, 21, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 0, 0, 0, 22, 22, 14, 14, 0, 20, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 0, 22, 22, 14, 14, 0, 0, 0, 21, 21, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 21, 21, 16, 16, 16, 16, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 21, 21, 21, 16, 16, 16, 16, 16, 16, 16, 16, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 0, 22, 17, 17, 17, 17, 13, 13, 13, 13, 14, 0, 0, 23, 19, 0, 0, 0, 0, 0, 22, 22, 14, 14, 0, 0, 0, 0, 0, 23, 19, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD e.val 0
def witnessLower (e : Fin 1024) : Fin 5 := ⟨witnessCode e / 5 % 5, Nat.mod_lt _ (by decide)⟩
def witnessUpper (e : Fin 1024) : Fin 5 := ⟨witnessCode e % 5, Nat.mod_lt _ (by decide)⟩
def excluded (e : Fin 1024) : Prop :=
  let a := (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1
  let b := (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2
  0 ≤ a * 89 + b * 57 ∧ 0 ≤ a * 171 + b * 89 ∧
  (0 < a * 89 + b * 57 ∨ 0 < a * 171 + b * 89)
instance (e : Fin 1024) : Decidable (excluded e) := by unfold excluded; infer_instance
theorem feasibility_check : ∀ e : Fin 1024, e.val ∈ edges ∨ excluded e := by decide +kernel
theorem feasible_mem_edges (e : Fin 1024) (r : ℝ) (hl : (89 : ℝ) / 57 < r) (hu : r < (171 : ℝ) / 89) (h : Feasible e.val r) : e.val ∈ edges := by
  rcases feasibility_check e with hedge | hex
  · exact hedge
  · exfalso
    rcases hex with ⟨hleft, hright, hstrict⟩
    have hleftR : (0 : ℝ) ≤ (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 89 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 57 := by exact_mod_cast hleft
    have hrightR : (0 : ℝ) ≤ (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 171 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 89 := by exact_mod_cast hright
    have positive := positive_inside_band
      ((discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 : ℝ)
      ((discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 : ℝ)
      (89/57) (171/89) r hl hu (by nlinarith) (by nlinarith) (by
        rcases hstrict with hstrict | hstrict
        · left; have hs : (0 : ℝ) < (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 89 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 57 := by exact_mod_cast hstrict
          nlinarith
        · right; have hs : (0 : ℝ) < (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 171 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 89 := by exact_mod_cast hstrict
          nlinarith)
    exact (not_lt_of_ge (h (witnessLower e) (witnessUpper e))) positive
end LambdaCantor.Integer.Band2
