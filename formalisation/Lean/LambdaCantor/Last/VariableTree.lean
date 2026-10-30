import LambdaCantor.Last.ReturnWords
import LambdaCantor.Last.ReturnTree

noncomputable section
namespace LambdaCantor.Last

/-- Splitting for interior nonlinear fibres requires no uniform upper depth. -/
structure VariableWordSystem (State : Type*) where
  word : State → Bool → List (Bool × Bool)
  next : State → Bool → State
  length_pos : ∀ state bit, 0 < (word state bit).length

namespace VariableWordSystem
variable {State : Type*} (system : VariableWordSystem State)

def run (system : VariableWordSystem State) (initial : State) (branch : ℕ → Bool) :
    ℕ → State × List (Bool × Bool)
  | 0 => (initial, [])
  | depth + 1 =>
    (system.next (run system initial branch depth).1 (branch depth),
      (run system initial branch depth).2 ++
        system.word (run system initial branch depth).1 (branch depth))

theorem run_prefix (initial : State) (first second : ℕ → Bool) (depth : ℕ)
    (agreement : ∀ position < depth, first position = second position) :
    system.run initial first depth = system.run initial second depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    simp only [run, ih (fun position before => agreement position (Nat.lt.step before)),
      agreement depth (Nat.lt_succ_self depth)]

theorem run_length (initial : State) (branch : ℕ → Bool) (depth : ℕ) :
    depth ≤ (system.run initial branch depth).2.length := by
  induction depth with
  | zero => simp [run]
  | succ depth ih =>
    have hpositive := system.length_pos (system.run initial branch depth).1 (branch depth)
    simp only [run, List.length_append]
    omega

def compactTree (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (initial : State) : CompactReturnTree (ℝ × ℝ) where
  cell branch depth := wordCylinder ratio (system.run initial branch depth).2
  nonempty branch depth := wordCylinder_nonempty _ _
  compact branch depth := isCompact_wordCylinder hpositive.le hless _
  nested branch depth := by
    simpa only [run] using wordCylinder_append_subset hpositive.le hless
      (system.run initial branch depth).2
      (system.word (system.run initial branch depth).1 (branch depth))
  prefix_agreement first second depth agreement := by
    rw [system.run_prefix initial first second depth agreement]
  diameterBound depth := ratio ^ depth
  bound_tendsto := tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless
  dist_bound branch depth first hfirst second hsecond :=
    (wordCylinder_dist_le hpositive.le hless _ hfirst hsecond).trans
      (pow_le_pow_of_le_one hpositive.le hless.le (system.run_length initial branch depth))

theorem coding_mem_dust (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (initial : State) (branch : ℕ → Bool) :
    (system.compactTree ratio hpositive hless initial).coding branch ∈ cantorDust ratio :=
  wordCylinder_subset_dust hpositive.le hless _
    ((system.compactTree ratio hpositive hless initial).coding_mem branch 0)

/-- Variable-depth sibling separation still makes the coding injective. -/
theorem coding_injective (ratio : ℝ) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (siblings : ∀ state first second, first ≠ second →
      WordsDiverge (system.word state first) (system.word state second))
    (initial : State) :
    Function.Injective
      (system.compactTree ratio hpositive (by linarith) initial).coding := by
  intro first second hequal
  by_contra hdifferent
  have hexists : ∃ position, first position ≠ second position := by
    by_contra hnone
    push_neg at hnone
    exact hdifferent (funext hnone)
  have hagreement : ∀ position < Nat.find hexists, first position = second position :=
    fun position before => not_ne_iff.mp (Nat.find_min hexists before)
  have hequal_run := system.run_prefix initial first second (Nat.find hexists) hagreement
  have hless : ratio < 1 := by linarith
  obtain ⟨firstTail, hfirstTail, hfirstEq⟩ :=
    (system.compactTree ratio hpositive hless initial).coding_mem first (Nat.find hexists + 1)
  obtain ⟨secondTail, hsecondTail, hsecondEq⟩ :=
    (system.compactTree ratio hpositive hless initial).coding_mem second (Nat.find hexists + 1)
  change wordMap ratio (system.run initial first (Nat.find hexists + 1)).2 firstTail = _ at hfirstEq
  change wordMap ratio (system.run initial second (Nat.find hexists + 1)).2 secondTail = _ at hsecondEq
  simp only [run, wordMap_append] at hfirstEq hsecondEq
  rw [← hequal_run] at hsecondEq
  have hgap := diverging_words_distance_gap hpositive hhalf
    (system.word (system.run initial first (Nat.find hexists)).1 (first (Nat.find hexists)))
    (system.word (system.run initial first (Nat.find hexists)).1 (second (Nat.find hexists)))
    (siblings _ _ _ (Nat.find_spec hexists)) _ (le_refl _) hfirstTail hsecondTail
  have hgap_positive : 0 <
      dist (wordMap ratio
        (system.word (system.run initial first (Nat.find hexists)).1 (first (Nat.find hexists))) firstTail)
        (wordMap ratio
        (system.word (system.run initial first (Nat.find hexists)).1 (second (Nat.find hexists))) secondTail) :=
    (mul_pos (by linarith) (pow_pos hpositive _)).trans_le hgap
  have hdist : 0 < dist
      ((system.compactTree ratio hpositive hless initial).coding first)
      ((system.compactTree ratio hpositive hless initial).coding second) := by
    rw [← hfirstEq, ← hsecondEq, wordMap_distance, abs_of_pos hpositive]
    exact mul_pos (pow_pos hpositive _) hgap_positive
  rw [hequal, dist_self] at hdist
  exact lt_irrefl _ hdist

/-- Strict corner bracketing at all stages survives the shrinking-cylinder limit. -/
theorem coding_level (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (initial : State) (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (hcontinuous : ContinuousOn function (cantorDust ratio))
    (hbrackets : ∀ branch depth,
      function (wordMap ratio (system.run initial branch depth).2 0) ≤ level ∧
      level ≤ function (wordMap ratio (system.run initial branch depth).2 (1, 1)))
    (branch : ℕ → Bool) :
    function ((system.compactTree ratio hpositive hless initial).coding branch) = level := by
  have hzero : (0 : ℝ × ℝ) ∈ cantorDust ratio :=
    ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩
  have hone : ((1 : ℝ), (1 : ℝ)) ∈ cantorDust ratio :=
    ⟨one_mem_cantorSet hpositive.le hless, one_mem_cantorSet hpositive.le hless⟩
  have hlower := (system.compactTree ratio hpositive hless initial).tendsto_of_mem_cells branch
    (fun depth => wordMap ratio (system.run initial branch depth).2 0)
    (fun depth => ⟨0, hzero, rfl⟩)
  have hupper := (system.compactTree ratio hpositive hless initial).tendsto_of_mem_cells branch
    (fun depth => wordMap ratio (system.run initial branch depth).2 (1, 1))
    (fun depth => ⟨(1, 1), hone, rfl⟩)
  have hlowerWithin := tendsto_nhdsWithin_iff.mpr ⟨hlower, Filter.Eventually.of_forall
    (fun depth => wordMap_mem_dust hpositive.le hless _ hzero)⟩
  have hupperWithin := tendsto_nhdsWithin_iff.mpr ⟨hupper, Filter.Eventually.of_forall
    (fun depth => wordMap_mem_dust hpositive.le hless _ hone)⟩
  have hvalue := hcontinuous _ (system.coding_mem_dust ratio hpositive hless initial branch)
  exact le_antisymm
    (le_of_tendsto' (hvalue.tendsto.comp hlowerWithin) (fun depth => (hbrackets branch depth).1))
    (ge_of_tendsto' (hvalue.tendsto.comp hupperWithin) (fun depth => (hbrackets branch depth).2))

end VariableWordSystem
end LambdaCantor.Last
