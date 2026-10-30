import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Fin
import Lean.Elab.Tactic.Decide
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.RationalPowers

/-- The complete small residue table is generated from its defining ranges.
Its length, not a Python count, is checked below. -/
def lowResiduePairs : List (ℕ × ℕ) :=
  (List.range 108).flatMap (fun offset =>
    ((List.range (offset+2)).filter (fun residue => decide (0 < residue ∧ residue.Coprime (offset+2)))).map
      (fun residue => (offset+2,residue)))

theorem lowResiduePairs_valid (pair : ℕ × ℕ) (membership : pair ∈ lowResiduePairs) :
    2 ≤ pair.1 ∧ pair.1 ≤ 109 ∧ 0 < pair.2 ∧ pair.2 < pair.1 ∧ pair.2.Coprime pair.1 := by
  obtain ⟨offset, offset_mem, selected⟩ := List.mem_flatMap.mp membership
  obtain ⟨residue, residue_mem, rfl⟩ := List.mem_map.mp selected
  have offset_bound := List.mem_range.mp offset_mem
  have selected := List.mem_filter.mp residue_mem
  have residue_bound := List.mem_range.mp selected.1
  have residue_valid : 0 < residue ∧ residue.Coprime (offset+2) := of_decide_eq_true selected.2
  exact ⟨by omega, by omega, residue_valid.1, residue_bound, residue_valid.2⟩

theorem lowResiduePairs_complete (denominator residue : ℕ)
    (denominator_lower : 2 ≤ denominator) (denominator_upper : denominator ≤ 109)
    (residue_positive : 0 < residue) (residue_upper : residue < denominator)
    (coprime : residue.Coprime denominator) :
    (denominator,residue) ∈ lowResiduePairs := by
  apply List.mem_flatMap.mpr
  refine ⟨denominator-2, List.mem_range.mpr (by omega), ?_⟩
  have offset_identity : denominator-2+2 = denominator := by omega
  rw [offset_identity]
  apply List.mem_map.mpr
  refine ⟨residue, List.mem_filter.mpr ⟨List.mem_range.mpr residue_upper, ?_⟩, rfl⟩
  exact decide_eq_true_eq.mpr ⟨residue_positive,coprime⟩

/-- User-authorized native checks on only 3675 residue entries. Completeness
is proved above from the defining ranges, not inferred from this count. -/
theorem lowResiduePairs_length : lowResiduePairs.length = 3675 := by native_decide

theorem lowResiduePairs_nodup : lowResiduePairs.Nodup := by native_decide

/-- Integer part m=1,...,2186 and the complete reduced residue table. -/
abbrev LowRationalIndex := Fin 2186 × Fin lowResiduePairs.length

def lowRationalNumerator (index : LowRationalIndex) : ℕ :=
  (lowResiduePairs.get index.2).1*(index.1.val+1)+(lowResiduePairs.get index.2).2

def lowRationalDenominator (index : LowRationalIndex) : ℕ :=
  (lowResiduePairs.get index.2).1

theorem lowRationalIndex_card : Fintype.card LowRationalIndex = 8033550 := by
  simp only [LowRationalIndex, Fintype.card_prod, Fintype.card_fin, lowResiduePairs_length] <;> norm_num

theorem lowRationalIndex_division (index : LowRationalIndex) :
    lowRationalNumerator index/lowRationalDenominator index = index.1.val+1 := by
  have valid := lowResiduePairs_valid _ (List.get_mem lowResiduePairs index.2)
  dsimp only [lowRationalNumerator, lowRationalDenominator]
  rw [Nat.mul_add_div (by omega : 0 < (lowResiduePairs.get index.2).1),
    Nat.div_eq_of_lt valid.2.2.2.1, Nat.add_zero]

theorem lowRationalIndex_residue (index : LowRationalIndex) :
    lowRationalNumerator index%lowRationalDenominator index = (lowResiduePairs.get index.2).2 := by
  have valid := lowResiduePairs_valid _ (List.get_mem lowResiduePairs index.2)
  dsimp only [lowRationalNumerator, lowRationalDenominator]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add,
    Nat.mod_eq_of_lt valid.2.2.2.1, Nat.mod_mod]

theorem lowRationalIndex_valid (index : LowRationalIndex) :
    2 ≤ lowRationalDenominator index ∧ lowRationalDenominator index ≤ 109 ∧
    lowRationalDenominator index < lowRationalNumerator index ∧
    lowRationalNumerator index < 2187*lowRationalDenominator index ∧
    (lowRationalNumerator index).Coprime (lowRationalDenominator index) := by
  have valid := lowResiduePairs_valid _ (List.get_mem lowResiduePairs index.2)
  have denominator_positive : 0 < lowRationalDenominator index := by
    dsimp only [lowRationalDenominator]
    omega
  have integer_part_upper : index.1.val+1 ≤ 2186 := by omega
  have integer_part_lower : 1 ≤ index.1.val+1 := by omega
  have lower_product := mul_le_mul_of_nonneg_left integer_part_lower (Nat.zero_le (lowRationalDenominator index))
  have upper_product := mul_le_mul_of_nonneg_left integer_part_upper (Nat.zero_le (lowRationalDenominator index))
  refine ⟨valid.1, valid.2.1, ?_, ?_, ?_⟩
  · dsimp only [lowRationalNumerator, lowRationalDenominator] at *
    nlinarith [valid.2.2.1]
  · dsimp only [lowRationalNumerator, lowRationalDenominator] at *
    nlinarith [valid.2.2.2.1]
  · change Nat.gcd (lowRationalNumerator index) (lowRationalDenominator index) = 1
    rw [Nat.gcd_comm, Nat.gcd_rec, lowRationalIndex_residue]
    exact valid.2.2.2.2.gcd_eq_one

/-- Every reduced fraction in the required bounded domain occurs at an index.
The nonzero residue follows from reducedness and denominator at least two. -/
theorem lowRationalIndex_complete (numerator denominator : ℕ)
    (denominator_lower : 2 ≤ denominator) (denominator_upper : denominator ≤ 109)
    (numerator_lower : denominator < numerator) (numerator_upper : numerator < 2187*denominator)
    (coprime : numerator.Coprime denominator) :
    ∃ index : LowRationalIndex,
      lowRationalNumerator index = numerator ∧ lowRationalDenominator index = denominator := by
  have denominator_positive : 0 < denominator := by omega
  have residue_coprime : (numerator%denominator).Coprime denominator := by
    change Nat.gcd (numerator%denominator) denominator = 1
    rw [← Nat.gcd_rec denominator numerator, Nat.gcd_comm]
    exact coprime.gcd_eq_one
  have residue_positive : 0 < numerator%denominator := by
    by_contra absent
    have residue_zero : numerator%denominator = 0 := by omega
    have gcd_one := residue_coprime.gcd_eq_one
    rw [residue_zero, Nat.gcd_zero_left] at gcd_one
    omega
  have residue_upper : numerator%denominator < denominator := Nat.mod_lt _ denominator_positive
  have member := lowResiduePairs_complete denominator (numerator%denominator) denominator_lower denominator_upper
    residue_positive residue_upper residue_coprime
  obtain ⟨residueIndex, residue_identity⟩ := List.mem_iff_get.mp member
  have integer_part_positive : 0 < numerator/denominator := Nat.div_pos numerator_lower.le denominator_positive
  have integer_part_upper : numerator/denominator < 2187 :=
    (Nat.div_lt_iff_lt_mul denominator_positive).mpr numerator_upper
  let integerPart : Fin 2186 := ⟨numerator/denominator-1, by omega⟩
  refine ⟨(integerPart,residueIndex), ?_, ?_⟩
  · simp only [lowRationalNumerator, residue_identity]
    have integer_part_identity : integerPart.val+1 = numerator/denominator := by dsimp [integerPart]; omega
    rw [integer_part_identity]
    simpa only [Nat.mul_comm] using Nat.div_add_mod numerator denominator
  · simp only [lowRationalDenominator, residue_identity]

theorem lowRationalIndex_injective :
    Function.Injective (fun index : LowRationalIndex =>
      (lowRationalNumerator index,lowRationalDenominator index)) := by
  intro first second equality
  have division_equal := congrArg (fun pair : ℕ × ℕ => pair.1/pair.2) equality
  have residue_equal := congrArg (fun pair : ℕ × ℕ => pair.1%pair.2) equality
  have denominator_equal := congrArg Prod.snd equality
  change lowRationalNumerator first/lowRationalDenominator first =
    lowRationalNumerator second/lowRationalDenominator second at division_equal
  change lowRationalNumerator first%lowRationalDenominator first =
    lowRationalNumerator second%lowRationalDenominator second at residue_equal
  rw [lowRationalIndex_division, lowRationalIndex_division] at division_equal
  rw [lowRationalIndex_residue, lowRationalIndex_residue] at residue_equal
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply lowResiduePairs_nodup.injective_get
    exact Prod.ext denominator_equal residue_equal

end LambdaCantor.RationalPowers

