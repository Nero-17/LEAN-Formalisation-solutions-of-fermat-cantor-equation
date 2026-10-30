import LambdaCantor.First.RootsKernelSelection

noncomputable section
namespace LambdaCantor.First.Roots

def parentWord {depth : ℕ} (word : Fin (depth + 1) → Bool × Bool) : Fin depth → Bool × Bool :=
  fun index => word index.castSucc

theorem admissible_parentWord {depth : ℕ} (selected : Set (ℕ → Bool × Bool))
    (word : Fin (depth + 1) → Bool × Bool)
    (admissible : ∃ representative ∈ selected, ∀ index : Fin (depth + 1), representative index = word index) :
    ∃ representative ∈ selected, ∀ index : Fin depth, representative index = parentWord word index := by
  obtain ⟨representative, member, agreement⟩ := admissible
  exact ⟨representative, member, fun index => agreement index.castSucc⟩

/-- The actual choices made by neighboring finite-prefix approximations lie
in the selected set and share precisely the prefix required by kernel coupling. -/
theorem refinement_representatives {depth : ℕ} (selected : Set (ℕ → Bool × Bool))
    (word : Fin (depth + 1) → Bool × Bool)
    (admissible : ∃ representative ∈ selected, ∀ index : Fin (depth + 1), representative index = word index) :
    prefixRepresentative selected depth (parentWord word) ∈ selected ∧
    prefixRepresentative selected (depth + 1) word ∈ selected ∧
    (∀ index < depth, prefixRepresentative selected depth (parentWord word) index =
      prefixRepresentative selected (depth + 1) word index) ∧
    prefixRepresentative selected (depth + 1) word depth = word (Fin.last depth) := by
  refine ⟨prefixRepresentative_mem selected depth _ (admissible_parentWord selected word admissible),
    prefixRepresentative_mem selected (depth + 1) word admissible, ?_, ?_⟩
  · intro index before
    exact (prefixRepresentative_matches selected depth (parentWord word) ⟨index, before⟩).trans
      (prefixRepresentative_matches selected (depth + 1) word ⟨index, by omega⟩).symm
  · exact prefixRepresentative_matches selected (depth + 1) word (Fin.last depth)

end LambdaCantor.First.Roots
