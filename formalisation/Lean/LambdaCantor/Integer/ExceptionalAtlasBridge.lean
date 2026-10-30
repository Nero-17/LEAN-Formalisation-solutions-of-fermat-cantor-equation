import LambdaCantor.Integer.ExceptionalWordGeometry
import LambdaCantor.Last.ReturnAtlas
import Mathlib.Tactic.Choose

noncomputable section
namespace LambdaCantor.Integer.Exceptional

def encodeDigit (digit : Fin 4) : Bool × Bool :=
  (decide (2 ≤ digit.val), decide (digit.val % 2 = 1))

theorem encodeDigit_injective : Function.Injective encodeDigit := by
  decide

theorem encoded_wordMap (word : List (Fin 4)) (point : ℝ × ℝ) :
    Last.wordMap (1/3) (word.map encodeDigit) point = wordEmbedding word point := by
  induction word with
  | nil => rfl
  | cons digit remaining inductionHypothesis =>
    simp only [List.map_cons, Last.wordMap, wordEmbedding, inductionHypothesis]
    apply Prod.ext <;> fin_cases digit <;>
      norm_num [Last.digitPoint, encodeDigit, firstBit, secondBit]
      <;> ring

theorem separated_words_encode_diverge (first second : List (Fin 4))
    (separated : WordsSeparate first second) :
    Last.WordsDiverge (first.map encodeDigit) (second.map encodeDigit) := by
  induction first generalizing second with
  | nil => obtain ⟨index, impossible, _⟩ := separated; simp at impossible
  | cons firstDigit remaining inductionHypothesis =>
    cases second with
    | nil => obtain ⟨index, _, impossible, _⟩ := separated; simp at impossible
    | cons secondDigit remainingSecond =>
      by_cases heads_equal : firstDigit = secondDigit
      · subst secondDigit
        obtain ⟨index, first_length, second_length, different⟩ := separated
        cases index with
        | zero => simp at different
        | succ index =>
          have tail_separated : WordsSeparate remaining remainingSecond :=
            ⟨index, by simpa using first_length, by simpa using second_length, by simpa using different⟩
          obtain ⟨common, left, right, leftRest, rightRest, unequal, left_eq, right_eq⟩ :=
            inductionHypothesis remainingSecond tail_separated
          refine ⟨encodeDigit firstDigit :: common,left,right,leftRest,rightRest,unequal,?_,?_⟩
          · simp only [List.map_cons, List.cons_append, left_eq]
          · simp only [List.map_cons, List.cons_append, right_eq]
      · exact ⟨[],encodeDigit firstDigit,encodeDigit secondDigit,remaining.map encodeDigit,
          remainingSecond.map encodeDigit,fun equality => heads_equal (encodeDigit_injective equality),rfl,rfl⟩

def slopeLinear (slope : ℝ) : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  (slope/2) • LinearMap.fst ℝ ℝ ℝ + (1/2 : ℝ) • LinearMap.snd ℝ ℝ ℝ

theorem slopeLinear_apply (slope : ℝ) (point : ℝ × ℝ) :
    slopeLinear slope point = (slope*point.1+point.2)/2 := by
  simp [slopeLinear]
  <;> ring

theorem encoded_linearWordReturn (slope level : ℝ) (word : List (Fin 4)) :
    Last.linearWordReturn (1/3) (slopeLinear slope) (word.map encodeDigit) level =
      returnLevel (geometricOffset slope) word level := by
  unfold Last.linearWordReturn Last.returnLevel
  rw [List.length_map, encoded_wordMap, slopeLinear_apply, returnLevel_geometric]
  rw [show (0 : ℝ × ℝ) = (0,0) from rfl]
  simp only [one_div, inv_pow]
  field_simp
  <;> ring

def encodedReturnPair (first second : List (Fin 4)) (separated : WordsSeparate first second) :
    Last.ReturnPair where
  word := fun bit => if bit then second.map encodeDigit else first.map encodeDigit
  length_pos := by
    intro bit
    have positive := separated_words_positive_length first second separated
    cases bit with
    | false => simpa using positive.1
    | true => simpa using positive.2
  diverge := separated_words_encode_diverge first second separated

theorem finiteReturnAtlas_of_twoReturns (slope margin : ℝ) (depth : ℕ)
    (levels targets : Set ℝ) (margin_positive : 0 < margin)
    (returns : ∀ level ∈ levels, TwoReturns (geometricOffset slope) targets depth level)
    (robust_targets : ∀ returned ∈ targets, ∀ value, dist value returned < margin → value ∈ levels) :
    ∃ atlas : Last.FiniteReturnAtlas (1/3) (slopeLinear slope) levels,
      atlas.maxDepth = depth ∧ atlas.margin = margin := by
  classical
  have witnesses : ∀ level : levels,
      ∃ first second : List (Fin 4), first.length ≤ depth ∧ second.length ≤ depth ∧
        WordsSeparate first second ∧ returnLevel (geometricOffset slope) first level ∈ targets ∧
        returnLevel (geometricOffset slope) second level ∈ targets :=
    fun level => returns level level.property
  choose first second first_length second_length separated first_return second_return using witnesses
  refine ⟨{
    pair := fun level => encodedReturnPair (first level) (second level) (separated level)
    maxDepth := depth
    length_le := ?_
    margin := margin
    margin_pos := margin_positive
    robust := ?_
  },rfl,rfl⟩
  · intro level bit
    cases bit with
    | false => simpa [encodedReturnPair] using first_length level
    | true => simpa [encodedReturnPair] using second_length level
  · intro level values close bit
    cases bit with
    | false =>
      apply robust_targets _ (first_return level) (values false)
      simpa only [encodedReturnPair, Bool.false_eq_true, if_false, encoded_linearWordReturn] using close false
    | true =>
      apply robust_targets _ (second_return level) (values true)
      simpa only [encodedReturnPair, if_true, encoded_linearWordReturn] using close true

theorem trimmed_intervals_robust (levels targets : Set ℝ) (margin : ℝ)
    (trimmed : ∀ returned ∈ targets, ∃ lower upper : ℝ,
      lower+margin ≤ returned ∧ returned ≤ upper-margin ∧ Set.Icc lower upper ⊆ levels) :
    ∀ returned ∈ targets, ∀ value, dist value returned < margin → value ∈ levels := by
  intro returned membership value close
  obtain ⟨lower,upper,lower_bound,upper_bound,contained⟩ := trimmed returned membership
  rw [Real.dist_eq, abs_lt] at close
  apply contained
  constructor <;> linarith [close.1,close.2]

end LambdaCantor.Integer.Exceptional
