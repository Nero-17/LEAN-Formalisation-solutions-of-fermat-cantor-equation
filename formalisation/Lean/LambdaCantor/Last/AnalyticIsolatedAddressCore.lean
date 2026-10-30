import LambdaCantor.Last.ReturnWords
import LambdaCantor.Addresses

noncomputable section
namespace LambdaCantor.Last
def pairedAddressPrefix (digits : ℕ → Bool × Bool) : ℕ → List (Bool × Bool)
  | 0 => []
  | depth+1 => pairedAddressPrefix digits depth ++ [digits depth]

def pairedAddressTail (ratio : ℝ) (digits : ℕ → Bool × Bool) (depth : ℕ) : ℝ × ℝ :=
  (address ratio (fun index => (digits (index+depth)).1),
    address ratio (fun index => (digits (index+depth)).2))

theorem pairedAddressPrefix_length (digits : ℕ → Bool × Bool) (depth : ℕ) :
    (pairedAddressPrefix digits depth).length = depth := by
  induction depth with
  | zero => rfl
  | succ depth induction => simp [pairedAddressPrefix, induction]

theorem pairedAddressTail_mem_dust (ratio : ℝ) (digits : ℕ → Bool × Bool) (depth : ℕ) :
    pairedAddressTail ratio digits depth ∈ cantorDust ratio :=
  ⟨⟨fun index => (digits (index+depth)).1, rfl⟩,
    ⟨fun index => (digits (index+depth)).2, rfl⟩⟩

theorem pairedAddressTail_recurrence {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool × Bool) (depth : ℕ) :
    pairedAddressTail ratio digits depth =
      wordMap ratio [digits depth] (pairedAddressTail ratio digits (depth+1)) := by
  have first := address_first_digit nonnegative less_one (fun index => (digits (index+depth)).1)
  have second := address_first_digit nonnegative less_one (fun index => (digits (index+depth)).2)
  apply Prod.ext
  · simpa [pairedAddressTail, wordMap, digitPoint, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first
  · simpa [pairedAddressTail, wordMap, digitPoint, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

theorem pairedAddressPrefix_representation {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digits : ℕ → Bool × Bool) (depth : ℕ) :
    wordMap ratio (pairedAddressPrefix digits depth) (pairedAddressTail ratio digits depth) =
      pairedAddressTail ratio digits 0 := by
  induction depth with
  | zero => rfl
  | succ depth induction =>
    rw [pairedAddressPrefix, wordMap_append,
      ← pairedAddressTail_recurrence nonnegative less_one digits depth]
    exact induction


end LambdaCantor.Last

