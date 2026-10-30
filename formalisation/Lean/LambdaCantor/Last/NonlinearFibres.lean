import LambdaCantor.Last.NonlinearWords
import LambdaCantor.Last.VariableTree
import LambdaCantor.Last.UncountableCoding

noncomputable section
namespace LambdaCantor.Last

structure InteriorCylinder (ratio : ℝ) (function : (ℝ × ℝ) → ℝ) (level : ℝ) where
  word : List (Bool × Bool)
  interior_level : level ∈ Set.Ioo (function (wordMap ratio word 0))
    (function (wordMap ratio word (1, 1)))

theorem WordsDiverge.symm {first second : List (Bool × Bool)}
    (hdiverge : WordsDiverge first second) : WordsDiverge second first := by
  obtain ⟨common, firstDigit, secondDigit, firstRest, secondRest,
    hdifferent, hfirst, hsecond⟩ := hdiverge
  exact ⟨common, secondDigit, firstDigit, secondRest, firstRest,
    Ne.symm hdifferent, hsecond, hfirst⟩

structure InteriorSplit (ratio : ℝ) (function : (ℝ × ℝ) → ℝ) (level : ℝ)
    (parent : InteriorCylinder ratio function level) where
  word : Bool → List (Bool × Bool)
  length_pos : ∀ bit, 0 < (word bit).length
  diverge : WordsDiverge (word false) (word true)
  interior_level : ∀ bit, level ∈ Set.Ioo
    (function (wordMap ratio (parent.word ++ word bit) 0))
    (function (wordMap ratio (parent.word ++ word bit) (1, 1)))

theorem exists_interiorSplit
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : Continuous function)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hshell : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hoverlap : (1 - 2 * ratio) * upperT < ratio * lowerS)
    (parent : InteriorCylinder ratio function level) :
    Nonempty (InteriorSplit ratio function level parent) := by
  have hscale : 0 < ratio ^ parent.word.length := pow_pos hpositive _
  obtain ⟨first, second, hfirstLength, hsecondLength, hdiverge, hfirst, hsecond⟩ :=
    nonlinear_two_descendants (growth.word_restriction hpositive (by linarith) parent.word)
      (hcontinuous.comp (continuous_wordMap ratio parent.word)) hpositive hhalf
      (mul_pos hscale hlowerS) (mul_lt_mul_of_pos_left hslope hscale)
      (by nlinarith [mul_lt_mul_of_pos_left hshell hscale])
      (by nlinarith [mul_lt_mul_of_pos_left hoverlap hscale]) parent.interior_level
  refine ⟨{ word := fun bit => if bit then second else first
            length_pos := ?_
            diverge := hdiverge
            interior_level := ?_ }⟩
  · intro bit
    cases bit <;> simp_all
  · intro bit
    cases bit
    · simpa [wordMap_append, Function.comp_apply] using hfirst
    · simpa [wordMap_append, Function.comp_apply] using hsecond

def interiorWordSystem {ratio : ℝ} {function : (ℝ × ℝ) → ℝ} {level : ℝ}
    (splitting : ∀ parent : InteriorCylinder ratio function level,
      InteriorSplit ratio function level parent) :
    VariableWordSystem (InteriorCylinder ratio function level) where
  word parent := (splitting parent).word
  next parent bit := ⟨parent.word ++ (splitting parent).word bit,
    (splitting parent).interior_level bit⟩
  length_pos parent := (splitting parent).length_pos

theorem interiorWordSystem_run_word {ratio : ℝ} {function : (ℝ × ℝ) → ℝ} {level : ℝ}
    (splitting : ∀ parent : InteriorCylinder ratio function level,
      InteriorSplit ratio function level parent)
    (initial : InteriorCylinder ratio function level) (branch : ℕ → Bool) (depth : ℕ) :
    ((interiorWordSystem splitting).run initial branch depth).1.word =
      initial.word ++ ((interiorWordSystem splitting).run initial branch depth).2 := by
  induction depth with
  | zero => simp [VariableWordSystem.run]
  | succ depth ih =>
    change ((interiorWordSystem splitting).run initial branch depth).1.word ++
        (splitting ((interiorWordSystem splitting).run initial branch depth).1).word (branch depth) =
      initial.word ++ (((interiorWordSystem splitting).run initial branch depth).2 ++
        (splitting ((interiorWordSystem splitting).run initial branch depth).1).word (branch depth))
    rw [ih, List.append_assoc]

/-- The global derivative inequalities already force every strict interior fibre
to be uncountable, before any uniform return-depth or dimension argument. -/
theorem nonlinear_interior_fibre_uncountable
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : Continuous function)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hshell : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hoverlap : (1 - 2 * ratio) * upperT < ratio * lowerS)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1))) :
    ¬ {point | point ∈ cantorDust ratio ∧ function point = level}.Countable := by
  let splitting : ∀ parent : InteriorCylinder ratio function level,
      InteriorSplit ratio function level parent := fun parent =>
    Classical.choice (exists_interiorSplit growth hcontinuous hpositive hhalf
      hlowerS hslope hshell hoverlap parent)
  let initial : InteriorCylinder ratio function level :=
    ⟨[], by change function (0, 0) < level ∧ level < function (1, 1); exact hlevel⟩
  have hless : ratio < 1 := by linarith
  apply uncountable_of_injective_binary_coding
    ((interiorWordSystem splitting).compactTree ratio hpositive hless initial).coding
  · apply (interiorWordSystem splitting).coding_injective ratio hpositive hhalf
    intro state first second hdifferent
    cases first <;> cases second
    · exact (hdifferent rfl).elim
    · exact (splitting state).diverge
    · exact (splitting state).diverge.symm
    · exact (hdifferent rfl).elim
  · intro branch
    refine ⟨(interiorWordSystem splitting).coding_mem_dust ratio hpositive hless initial branch, ?_⟩
    apply (interiorWordSystem splitting).coding_level ratio hpositive hless initial
      function level hcontinuous.continuousOn _ branch
    intro other depth
    have hstate := ((interiorWordSystem splitting).run initial other depth).1.interior_level
    rw [interiorWordSystem_run_word] at hstate
    simpa only [initial, List.nil_append] using ⟨hstate.1.le, hstate.2.le⟩

end LambdaCantor.Last
