import LambdaCantor.First.WordTree

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory
open scoped ENNReal NNReal

def addressPoint (ratio : ℝ) (digits : ℕ → Bool × Bool) : ℝ × ℝ :=
  (address ratio (fun position => (digits position).1),
   address ratio (fun position => (digits position).2))

def dustCylinder (ratio : ℝ) {depth : ℕ} (word : Fin depth → Bool × Bool) : Set (ℝ × ℝ) :=
  addressPoint ratio '' prefixCylinder word

theorem dustCylinder_parent (ratio : ℝ) {prefixLength block : ℕ}
    (word : Fin (prefixLength + block) → Bool × Bool) :
    dustCylinder ratio word ⊆ dustCylinder ratio (wordParent word) := by
  rintro point ⟨digits, hdigits, rfl⟩
  exact ⟨digits, prefixCylinder_parent hdigits, rfl⟩

theorem dustCylinder_ediam {ratio : ℝ} (hratio : 0 ≤ ratio) (hcontract : ratio < 1)
    {depth : ℕ} (word : Fin depth → Bool × Bool) :
    Metric.ediam (dustCylinder ratio word) ≤ ENNReal.ofReal ratio ^ depth := by
  rw [Metric.ediam_le_iff]
  rintro _ ⟨left, hleft, rfl⟩ _ ⟨right, hright, rfl⟩
  have hsame : ∀ position < depth, left position = right position := by
    intro position hposition
    exact (hleft ⟨position, hposition⟩).trans (hright ⟨position, hposition⟩).symm
  have hx := address_close_of_prefix hratio hcontract
    (fun position hposition => congrArg Prod.fst (hsame position hposition))
  have hy := address_close_of_prefix hratio hcontract
    (fun position hposition => congrArg Prod.snd (hsame position hposition))
  rw [← ENNReal.ofReal_pow hratio]
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  simpa only [addressPoint, Prod.dist_eq, Real.dist_eq] using max_le hx hy

def activeWords (ratio : ℝ) (target : Set (ℝ × ℝ)) (depth : ℕ) :
    Finset (Fin depth → Bool × Bool) := by
  classical
  exact Finset.univ.filter fun word => (dustCylinder ratio word ∩ target).Nonempty

theorem mem_activeWords (ratio : ℝ) (target : Set (ℝ × ℝ)) {depth : ℕ}
    (word : Fin depth → Bool × Bool) :
    word ∈ activeWords ratio target depth ↔ (dustCylinder ratio word ∩ target).Nonempty := by
  classical
  simp [activeWords]

theorem activeWords_parent (ratio : ℝ) (target : Set (ℝ × ℝ)) {prefixLength block : ℕ}
    {word : Fin (prefixLength + block) → Bool × Bool}
    (hword : word ∈ activeWords ratio target (prefixLength + block)) :
    wordParent word ∈ activeWords ratio target prefixLength := by
  rw [mem_activeWords] at hword ⊢
  obtain ⟨point, hpoint, htarget⟩ := hword
  exact ⟨point, dustCylinder_parent ratio word hpoint, htarget⟩

theorem activeWords_cover (ratio : ℝ) (target : Set (ℝ × ℝ))
    (hsubset : target ⊆ (cantorSet ratio).prod (cantorSet ratio)) (depth : ℕ) :
    target ⊆ ⋃ word ∈ activeWords ratio target depth, dustCylinder ratio word := by
  intro point hpoint
  obtain ⟨⟨left, hleft⟩, ⟨right, hright⟩⟩ := hsubset hpoint
  let digits : ℕ → Bool × Bool := fun position => (left position, right position)
  let word : Fin depth → Bool × Bool := fun position => digits position
  have hcylinder : point ∈ dustCylinder ratio word := by
    refine ⟨digits, (fun _ => rfl), ?_⟩
    exact Prod.ext hleft hright
  exact Set.mem_iUnion₂.2 ⟨word, (mem_activeWords ratio target word).2
    ⟨point, hcylinder, hpoint⟩, hcylinder⟩

end LambdaCantor.First.PrefixSlopes

