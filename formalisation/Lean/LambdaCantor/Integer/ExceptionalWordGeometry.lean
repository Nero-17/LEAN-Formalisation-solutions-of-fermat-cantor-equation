import LambdaCantor.Integer.ExceptionalReturnSemantics
import LambdaCantor.Classical.Source
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.Integer.Exceptional

def firstBit (digit : Fin 4) : ℝ := if digit.val < 2 then 0 else 2
def secondBit (digit : Fin 4) : ℝ := if digit.val % 2 = 0 then 0 else 2

def wordEmbedding : List (Fin 4) → (ℝ × ℝ) → (ℝ × ℝ)
  | [], point => point
  | digit :: remaining, point =>
      ((firstBit digit + (wordEmbedding remaining point).1)/3,
       (secondBit digit + (wordEmbedding remaining point).2)/3)

def geometricOffset (slope : ℝ) (digit : Fin 4) : ℝ :=
  (slope * firstBit digit + secondBit digit)/2

theorem separated_words_positive_length (firstWord secondWord : List (Fin 4))
    (separated : WordsSeparate firstWord secondWord) :
    0 < firstWord.length ∧ 0 < secondWord.length := by
  obtain ⟨index, first_length, second_length, different⟩ := separated
  omega

theorem geometricOffset_values (slope : ℝ) :
    geometricOffset slope 0 = 0 ∧ geometricOffset slope 1 = 1 ∧
      geometricOffset slope 2 = slope ∧ geometricOffset slope 3 = slope+1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [geometricOffset, firstBit, secondBit] <;> ring

theorem geometricOffset_eq_certified (slope : ℚ) (denominator : ℤ) (offsets : Fin 4 → ℤ)
    (certified : ∀ digit : Fin 4, (offsets digit : ℚ)/denominator =
      match digit.val with | 0 => 0 | 1 => 1 | 2 => slope | _ => slope+1) :
    (fun digit => (offsets digit : ℝ)/(denominator : ℝ)) = geometricOffset (slope : ℝ) := by
  funext digit
  have zero_value : (offsets 0 : ℝ)/(denominator : ℝ) = 0 := by
    exact_mod_cast certified 0
  have one_value : (offsets 1 : ℝ)/(denominator : ℝ) = 1 := by
    exact_mod_cast certified 1
  have two_value : (offsets 2 : ℝ)/(denominator : ℝ) = (slope : ℝ) := by
    exact_mod_cast certified 2
  have three_value : (offsets 3 : ℝ)/(denominator : ℝ) = (slope : ℝ)+1 := by
    exact_mod_cast certified 3
  obtain ⟨zero_offset, one_offset, two_offset, three_offset⟩ :=
    geometricOffset_values (slope : ℝ)
  fin_cases digit
  · exact zero_value.trans zero_offset.symm
  · exact one_value.trans one_offset.symm
  · exact two_value.trans two_offset.symm
  · exact three_value.trans three_offset.symm

theorem wordEmbedding_cantor (word : List (Fin 4)) (point : ℝ × ℝ)
    (membership : point ∈ cantorSet (1/3) ×ˢ cantorSet (1/3)) :
    wordEmbedding word point ∈ cantorSet (1/3) ×ˢ cantorSet (1/3) := by
  induction word with
  | nil => exact membership
  | cons digit remaining inductionHypothesis =>
    have first_member := inductionHypothesis.1
    have second_member := inductionHypothesis.2
    rw [cantorSet_third_eq] at first_member second_member
    change _ ∈ cantorSet (1/3) ∧ _ ∈ cantorSet (1/3)
    simp only [cantorSet_third_eq]
    constructor
    · change (firstBit digit + (wordEmbedding remaining point).1)/3 ∈ _root_.cantorSet
      unfold firstBit
      split
      · simpa only [zero_add] using Classical.cantor_prepend_zero first_member
      · exact Classical.cantor_prepend_two first_member
    · change (secondBit digit + (wordEmbedding remaining point).2)/3 ∈ _root_.cantorSet
      unfold secondBit
      split
      · simpa only [zero_add] using Classical.cantor_prepend_zero second_member
      · exact Classical.cantor_prepend_two second_member

theorem wordEmbedding_affine (word : List (Fin 4)) (point : ℝ × ℝ) :
    wordEmbedding word point =
      ((wordEmbedding word (0,0)).1 + point.1 / 3^word.length,
       (wordEmbedding word (0,0)).2 + point.2 / 3^word.length) := by
  induction word with
  | nil => simp [wordEmbedding]
  | cons digit remaining inductionHypothesis =>
    simp only [wordEmbedding, List.length_cons, inductionHypothesis]
    apply Prod.ext <;> dsimp <;> rw [pow_succ] <;> field_simp <;> ring

theorem wordEmbedding_append (firstWord secondWord : List (Fin 4)) (point : ℝ × ℝ) :
    wordEmbedding (firstWord++secondWord) point =
      wordEmbedding firstWord (wordEmbedding secondWord point) := by
  induction firstWord with
  | nil => rfl
  | cons digit remaining inductionHypothesis =>
    simp only [List.cons_append, wordEmbedding, inductionHypothesis]

theorem wordEmbedding_distance (word : List (Fin 4)) (first second : ℝ × ℝ) :
    dist (wordEmbedding word first) (wordEmbedding word second) =
      dist first second / (3:ℝ)^word.length := by
  rw [wordEmbedding_affine word first, wordEmbedding_affine word second]
  simp only [Prod.dist_eq, Real.dist_eq]
  have horizontal : (wordEmbedding word (0,0)).1+first.1/(3:ℝ)^word.length -
      ((wordEmbedding word (0,0)).1+second.1/(3:ℝ)^word.length) =
      (first.1-second.1)/(3:ℝ)^word.length := by ring
  have vertical : (wordEmbedding word (0,0)).2+first.2/(3:ℝ)^word.length -
      ((wordEmbedding word (0,0)).2+second.2/(3:ℝ)^word.length) =
      (first.2-second.2)/(3:ℝ)^word.length := by ring
  rw [horizontal,vertical,abs_div,abs_div,abs_of_pos (by positivity : 0 < (3:ℝ)^word.length)]
  exact max_div_div_right (by positivity : 0 ≤ (3:ℝ)^word.length) _ _

theorem returnLevel_geometric (slope level : ℝ) (word : List (Fin 4)) :
    returnLevel (geometricOffset slope) word level =
      3^word.length * (level -
        (slope*(wordEmbedding word (0,0)).1+(wordEmbedding word (0,0)).2)/2) := by
  induction word generalizing level with
  | nil => simp [returnLevel, wordEmbedding]
  | cons digit remaining inductionHypothesis =>
    rw [returnLevel, inductionHypothesis]
    simp only [wordEmbedding, List.length_cons, geometricOffset, pow_succ]
    ring

theorem first_digit_unique (firstDigit secondDigit : Fin 4) (first second : ℝ × ℝ)
    (first_bounds : first ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    (second_bounds : second ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1)
    (first_equal : (firstBit firstDigit+first.1)/3 = (firstBit secondDigit+second.1)/3)
    (second_equal : (secondBit firstDigit+first.2)/3 = (secondBit secondDigit+second.2)/3) :
    firstDigit = secondDigit := by
  rcases first_bounds with ⟨⟨first_lower,first_upper⟩,⟨second_lower,second_upper⟩⟩
  rcases second_bounds with ⟨⟨third_lower,third_upper⟩,⟨fourth_lower,fourth_upper⟩⟩
  fin_cases firstDigit <;> fin_cases secondDigit <;>
    norm_num [firstBit, secondBit] at first_equal second_equal ⊢ <;> linarith

/-- The certificate's finite disagreement condition certifies disjoint actual
Cantor cylinders, even when the two return words have different lengths. -/
theorem separated_words_distinct (firstWord secondWord : List (Fin 4))
    (separated : WordsSeparate firstWord secondWord) (first second : ℝ × ℝ)
    (first_member : first ∈ cantorSet (1/3) ×ˢ cantorSet (1/3))
    (second_member : second ∈ cantorSet (1/3) ×ˢ cantorSet (1/3)) :
    wordEmbedding firstWord first ≠ wordEmbedding secondWord second := by
  induction firstWord generalizing secondWord with
  | nil => obtain ⟨index, impossible, _⟩ := separated; simp at impossible
  | cons firstDigit remaining inductionHypothesis =>
    cases secondWord with
    | nil => obtain ⟨index, _, impossible, _⟩ := separated; simp at impossible
    | cons secondDigit remainingSecond =>
      intro equality
      have first_coordinate := congrArg Prod.fst equality
      have second_coordinate := congrArg Prod.snd equality
      change (firstBit firstDigit+(wordEmbedding remaining first).1)/3 =
        (firstBit secondDigit+(wordEmbedding remainingSecond second).1)/3 at first_coordinate
      change (secondBit firstDigit+(wordEmbedding remaining first).2)/3 =
        (secondBit secondDigit+(wordEmbedding remainingSecond second).2)/3 at second_coordinate
      have first_tail := wordEmbedding_cantor remaining first first_member
      have second_tail := wordEmbedding_cantor remainingSecond second second_member
      have first_bounds : wordEmbedding remaining first ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 :=
        ⟨LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) first_tail.1,
         LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) first_tail.2⟩
      have second_bounds : wordEmbedding remainingSecond second ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1 :=
        ⟨LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) second_tail.1,
         LambdaCantor.cantorSet_subset_unitInterval (by norm_num) (by norm_num) second_tail.2⟩
      have digits_equal := first_digit_unique firstDigit secondDigit _ _ first_bounds second_bounds
        first_coordinate second_coordinate
      subst secondDigit
      have tails_equal : wordEmbedding remaining first = wordEmbedding remainingSecond second := by
        apply Prod.ext <;> linarith
      obtain ⟨index, first_length, second_length, different⟩ := separated
      cases index with
      | zero => simp at different
      | succ index =>
        have tail_separated : WordsSeparate remaining remainingSecond := by
          refine ⟨index, by simpa using first_length, by simpa using second_length, ?_⟩
          simpa using different
        exact inductionHypothesis remainingSecond tail_separated tails_equal

end LambdaCantor.Integer.Exceptional
