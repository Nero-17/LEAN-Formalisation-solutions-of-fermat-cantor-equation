import Mathlib.Data.Set.Countable
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin

namespace LambdaCantor.Integer

/-- Removing all countable members of a countable family leaves an
uncountable set of points whose family-neighbourhoods are all uncountable. -/
theorem uncountable_core_of_countable_family {X Index : Type*} [Countable Index]
    (s : Set X) (uncountable : ¬ s.Countable) (family : Index → Set X) :
    ¬ {x | x ∈ s ∧ ∀ i, x ∈ family i → ¬ (s ∩ family i).Countable}.Countable := by
  classical
  let bad : Set X := ⋃ i : Index, if (s ∩ family i).Countable then s ∩ family i else ∅
  have hbad : bad.Countable := by
    apply Set.countable_iUnion
    intro i
    split_ifs with h
    · exact h
    · exact Set.countable_empty
  intro hcore
  apply uncountable
  apply (hbad.union hcore).mono
  intro x hx
  by_cases hb : x ∈ bad
  · exact Or.inl hb
  · right
    refine ⟨hx, ?_⟩
    intro i hxi hcount
    apply hb
    apply Set.mem_iUnion.mpr
    exact ⟨i, by simp only [if_pos hcount]; exact ⟨hx, hxi⟩⟩

/-- A finite alphabet word, retaining its length as part of the index. -/
def PrefixIndex (alphabet : Type*) := Σ depth : ℕ, Fin depth → alphabet

instance {alphabet : Type*} [Fintype alphabet] : Countable (PrefixIndex alphabet) :=
  inferInstanceAs (Countable (Σ depth : ℕ, Fin depth → alphabet))

def prefixCylinder {alphabet : Type*} (word : PrefixIndex alphabet) :
    Set (ℕ → alphabet) := {digits | ∀ j : Fin word.1, digits j.val = word.2 j}

/-- In an uncountable set of infinite addresses, some node has two
uncountable immediate children. This proves the tree-theoretic step in the
irrational-tangent argument without assuming any geometric return lemma. -/
theorem uncountable_addresses_branch {alphabet : Type*} [Fintype alphabet]
    (s : Set (ℕ → alphabet)) (uncountable : ¬ s.Countable) :
    ∃ left ∈ s, ∃ right ∈ s, ∃ depth : ℕ,
      (∀ j < depth, left j = right j) ∧ left depth ≠ right depth ∧
      ¬ (s ∩ prefixCylinder ⟨depth+1, fun j => left j.val⟩).Countable ∧
      ¬ (s ∩ prefixCylinder ⟨depth+1, fun j => right j.val⟩).Countable := by
  classical
  let core : Set (ℕ → alphabet) :=
    {x | x ∈ s ∧ ∀ word : PrefixIndex alphabet,
      x ∈ prefixCylinder word → ¬ (s ∩ prefixCylinder word).Countable}
  have hcore : ¬ core.Countable :=
    uncountable_core_of_countable_family s uncountable prefixCylinder
  have nontrivial : core.Nontrivial := by
    by_contra h
    apply hcore
    have hs : core.Subsingleton := by
      intro x hx y hy
      by_contra hxy
      exact h ⟨x, hx, y, hy, hxy⟩
    exact hs.countable
  obtain ⟨left, hl, right, hr, different⟩ := nontrivial
  have exists_difference : ∃ depth, left depth ≠ right depth := by
    by_contra h
    apply different
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  refine ⟨left, hl.1, right, hr.1, Nat.find exists_difference, ?_,
    Nat.find_spec exists_difference, ?_, ?_⟩
  · intro j hj
    exact not_not.mp (Nat.find_min exists_difference hj)
  · exact hl.2 ⟨Nat.find exists_difference+1, fun j => left j.val⟩ (fun _ => rfl)
  · exact hr.2 ⟨Nat.find exists_difference+1, fun j => right j.val⟩ (fun _ => rfl)

end LambdaCantor.Integer
