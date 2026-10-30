import LambdaCantor.Certificates.IntegerGraph1
import LambdaCantor.Integer.Feasibility

set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace LambdaCantor.Integer.Band1
def witnessCode (e : Fin 1024) : ℕ := ([0, 0, 0, 0, 0, 23, 23, 23, 19, 19, 19, 0, 0, 0, 0, 22, 14, 0, 0, 0, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 0, 0, 22, 14, 0, 0, 0, 0, 23, 23, 23, 19, 19, 19, 0, 16, 16, 16, 16, 8, 8, 8, 8, 0, 23, 23, 23, 19, 19, 19, 0, 0, 21, 21, 21, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 9, 9, 9, 0, 0, 23, 23, 23, 19, 19, 19, 0, 16, 16, 16, 16, 8, 8, 8, 8, 0, 23, 23, 23, 19, 19, 19, 0, 0, 0, 0, 22, 14, 0, 0, 0, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 20, 20, 20, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 0, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 0, 0, 22, 14, 0, 20, 20, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 0, 22, 14, 0, 0, 0, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 20, 20, 20, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 0, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 0, 0, 22, 14, 0, 0, 0, 0, 23, 23, 23, 19, 19, 19, 0, 16, 16, 16, 16, 8, 8, 8, 8, 0, 23, 23, 23, 19, 19, 19, 0, 0, 21, 21, 21, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 9, 9, 9, 0, 0, 23, 23, 23, 19, 19, 19, 0, 16, 16, 16, 16, 8, 8, 8, 8, 0, 23, 23, 23, 19, 19, 19, 0, 0, 0, 0, 22, 14, 0, 0, 0, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 0, 0, 0, 22, 14, 0, 0, 0, 0, 23, 23, 23, 19, 19, 19, 0, 0, 0, 0, 0] : List ℕ).getD e.val 0
def witnessLower (e : Fin 1024) : Fin 5 := ⟨witnessCode e / 5 % 5, Nat.mod_lt _ (by decide)⟩
def witnessUpper (e : Fin 1024) : Fin 5 := ⟨witnessCode e % 5, Nat.mod_lt _ (by decide)⟩
def excluded (e : Fin 1024) : Prop :=
  let a := (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1
  let b := (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2
  0 ≤ a * 101 + b * 79 ∧ 0 ≤ a * 183 + b * 143 ∧
  (0 < a * 101 + b * 79 ∨ 0 < a * 183 + b * 143)
instance (e : Fin 1024) : Decidable (excluded e) := by unfold excluded; infer_instance
theorem feasibility_check : ∀ e : Fin 1024, e.val ∈ edges ∨ excluded e := by decide +kernel
theorem feasible_mem_edges (e : Fin 1024) (r : ℝ) (hl : (101 : ℝ) / 79 < r) (hu : r < (183 : ℝ) / 143) (h : Feasible e.val r) : e.val ∈ edges := by
  rcases feasibility_check e with hedge | hex
  · exact hedge
  · exfalso
    rcases hex with ⟨hleft, hright, hstrict⟩
    have hleftR : (0 : ℝ) ≤ (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 101 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 79 := by exact_mod_cast hleft
    have hrightR : (0 : ℝ) ≤ (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 183 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 143 := by exact_mod_cast hright
    have positive := positive_inside_band
      ((discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 : ℝ)
      ((discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 : ℝ)
      (101/79) (183/143) r hl hu (by nlinarith) (by nlinarith) (by
        rcases hstrict with hstrict | hstrict
        · left; have hs : (0 : ℝ) < (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 101 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 79 := by exact_mod_cast hstrict
          nlinarith
        · right; have hs : (0 : ℝ) < (discrepancy e.val (witnessLower e).val (witnessUpper e).val).1 * 183 + (discrepancy e.val (witnessLower e).val (witnessUpper e).val).2 * 143 := by exact_mod_cast hstrict
          nlinarith)
    exact (not_lt_of_ge (h (witnessLower e) (witnessUpper e))) positive
end LambdaCantor.Integer.Band1
