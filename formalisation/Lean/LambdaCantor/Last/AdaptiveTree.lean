import LambdaCantor.Last.ReturnWords
import LambdaCantor.Last.ReturnTree
import Lean.Elab.Tactic.Omega

noncomputable section
namespace LambdaCantor.Last

/-- State-dependent finite returns. States can contain the normalized error and
level; using a subtype records that the return invariants hold at every step. -/
structure AdaptiveWordSystem (State : Type*) where
  word : State → Bool → List (Bool × Bool)
  next : State → Bool → State
  maxDepth : ℕ
  length_pos : ∀ state bit, 0 < (word state bit).length
  length_le : ∀ state bit, (word state bit).length ≤ maxDepth

namespace AdaptiveWordSystem
variable {State : Type*} (system : AdaptiveWordSystem State)

/-- Simultaneously evolve the normalized state and concatenate the return words. -/
def run (system : AdaptiveWordSystem State) (initial : State) (branch : ℕ → Bool) :
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

theorem run_length_bounds (initial : State) (branch : ℕ → Bool) (depth : ℕ) :
    depth ≤ (system.run initial branch depth).2.length ∧
      (system.run initial branch depth).2.length ≤ depth * system.maxDepth := by
  induction depth with
  | zero => simp [run]
  | succ depth ih =>
    have hpos := system.length_pos (system.run initial branch depth).1 (branch depth)
    have hle := system.length_le (system.run initial branch depth).1 (branch depth)
    simp only [run, List.length_append, Nat.succ_mul]
    omega

/-- The cells used here are genuine Cantor cylinders. -/
def compactTree (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (initial : State) : CompactReturnTree (ℝ × ℝ) where
  cell branch depth := wordCylinder ratio (system.run initial branch depth).2
  nonempty branch depth := wordCylinder_nonempty _ _
  compact branch depth := isCompact_wordCylinder hpositive.le hless _
  nested branch depth := by
    simpa only [run] using wordCylinder_append_subset hpositive.le hless
      (system.run initial branch depth).2
      (system.word (system.run initial branch depth).1 (branch depth))
  prefix_agreement first second depth agreement := by rw [system.run_prefix initial first second depth agreement]
  diameterBound depth := ratio ^ depth
  bound_tendsto := tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless
  dist_bound branch depth first hfirst second hsecond :=
    (wordCylinder_dist_le hpositive.le hless _ hfirst hsecond).trans
      (pow_le_pow_of_le_one hpositive.le hless.le (system.run_length_bounds initial branch depth).1)

theorem coding_mem_dust (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (initial : State) (branch : ℕ → Bool) :
    (system.compactTree ratio hpositive hless initial).coding branch ∈ cantorDust ratio := by
  exact wordCylinder_subset_dust hpositive.le hless _
    ((system.compactTree ratio hpositive hless initial).coding_mem branch 0)

/-- A single-return residual identity iterates with the actual total cylinder depth. -/
theorem run_residual (ratio : ℝ) (residual : State → (ℝ × ℝ) → ℝ)
    (step_identity : ∀ state bit point,
      residual state (wordMap ratio (system.word state bit) point) =
        ratio ^ (system.word state bit).length * residual (system.next state bit) point)
    (initial : State) (branch : ℕ → Bool) (depth : ℕ) (point : ℝ × ℝ) :
    residual initial (wordMap ratio (system.run initial branch depth).2 point) =
      ratio ^ (system.run initial branch depth).2.length *
        residual (system.run initial branch depth).1 point := by
  induction depth generalizing point with
  | zero => simp [run, wordMap]
  | succ depth ih =>
    simp only [run, wordMap_append, List.length_append, pow_add]
    rw [ih, step_identity]
    ring

/-- Bounded normalized residuals vanish at every limit point of the adaptive tree. -/
theorem coding_residual_zero (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (residual : State → (ℝ × ℝ) → ℝ)
    (step_identity : ∀ state bit point,
      residual state (wordMap ratio (system.word state bit) point) =
        ratio ^ (system.word state bit).length * residual (system.next state bit) point)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (bounded : ∀ state point, point ∈ cantorDust ratio → |residual state point| ≤ bound)
    (initial : State) (branch : ℕ → Bool) :
    residual initial ((system.compactTree ratio hpositive hless initial).coding branch) = 0 := by
  apply (system.compactTree ratio hpositive hless initial).coding_level
    (residual initial) 0 (fun depth => ratio ^ depth * bound)
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hpositive.le hless).mul_const bound)
    _ branch
  intro other depth point hpoint
  rcases hpoint with ⟨tail, htail, rfl⟩
  rw [sub_zero, system.run_residual ratio residual step_identity, abs_mul,
    abs_of_nonneg (pow_nonneg hpositive.le _)]
  exact (mul_le_mul_of_nonneg_left (bounded _ _ htail) (pow_nonneg hpositive.le _)).trans
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hpositive.le hless.le (system.run_length_bounds initial other depth).1) hbound)

/-- Uniform separation of sibling return cylinders gives geometric separation
of arbitrary coded branches. The weaker depth exponent is convenient for Frostman. -/
theorem coding_separation (ratio : ℝ) (hpositive : 0 < ratio) (hless : ratio < 1)
    (separation : ℝ) (hseparation : 0 ≤ separation)
    (siblings : ∀ state firstBit secondBit, firstBit ≠ secondBit →
      ∀ first ∈ cantorDust ratio, ∀ second ∈ cantorDust ratio,
        separation ≤ dist (wordMap ratio (system.word state firstBit) first)
          (wordMap ratio (system.word state secondBit) second))
    (initial : State) (depth : ℕ) (first second : ℕ → Bool)
    (different : ∃ position < depth, first position ≠ second position) :
    separation * ratio ^ (depth * system.maxDepth) ≤
      dist ((system.compactTree ratio hpositive hless initial).coding first)
        ((system.compactTree ratio hpositive hless initial).coding second) := by
  classical
  have exists_difference : ∃ position, first position ≠ second position :=
    ⟨different.choose, different.choose_spec.2⟩
  have before_depth : Nat.find exists_difference < depth :=
    (Nat.find_min' exists_difference different.choose_spec.2).trans_lt different.choose_spec.1
  have agreement : ∀ position < Nat.find exists_difference, first position = second position :=
    fun position before => not_ne_iff.mp (Nat.find_min exists_difference before)
  have equal_run := system.run_prefix initial first second (Nat.find exists_difference) agreement
  obtain ⟨firstTail, hfirstTail, hfirstEq⟩ :=
    (system.compactTree ratio hpositive hless initial).coding_mem first (Nat.find exists_difference + 1)
  obtain ⟨secondTail, hsecondTail, hsecondEq⟩ :=
    (system.compactTree ratio hpositive hless initial).coding_mem second (Nat.find exists_difference + 1)
  change wordMap ratio (system.run initial first (Nat.find exists_difference + 1)).2 firstTail = _ at hfirstEq
  change wordMap ratio (system.run initial second (Nat.find exists_difference + 1)).2 secondTail = _ at hsecondEq
  simp only [run, wordMap_append] at hfirstEq hsecondEq
  rw [← equal_run] at hsecondEq
  rw [← hfirstEq, ← hsecondEq, wordMap_distance, abs_of_pos hpositive]
  have length_le : (system.run initial first (Nat.find exists_difference)).2.length ≤
      depth * system.maxDepth :=
    (system.run_length_bounds initial first _).2.trans
      (Nat.mul_le_mul_right system.maxDepth before_depth.le)
  calc
    separation * ratio ^ (depth * system.maxDepth) ≤
        separation * ratio ^ (system.run initial first (Nat.find exists_difference)).2.length :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hpositive.le hless.le length_le) hseparation
    _ = ratio ^ (system.run initial first (Nat.find exists_difference)).2.length * separation := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (siblings _ _ _ (Nat.find_spec exists_difference) _ hfirstTail _ hsecondTail)
      (pow_nonneg hpositive.le _)

end AdaptiveWordSystem
end LambdaCantor.Last
