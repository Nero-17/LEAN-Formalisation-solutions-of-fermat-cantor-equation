import LambdaCantor.First.PrefixCylinder
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory
open scoped ENNReal NNReal

def wordParent {prefixLength block : ℕ} (word : Fin (prefixLength + block) → Bool × Bool) :
    Fin prefixLength → Bool × Bool := fun position => word (Fin.castAdd block position)

def wordSuffix {prefixLength block : ℕ} (word : Fin (prefixLength + block) → Bool × Bool) :
    Fin block → Bool × Bool := fun position => word (Fin.natAdd prefixLength position)

theorem word_eq_of_parent_suffix {prefixLength block : ℕ}
    {left right : Fin (prefixLength + block) → Bool × Bool}
    (hparent : wordParent left = wordParent right)
    (hsuffix : wordSuffix left = wordSuffix right) : left = right := by
  calc
    left = Fin.append (wordParent left) (wordSuffix left) :=
      Fin.append_castAdd_natAdd.symm
    _ = Fin.append (wordParent right) (wordSuffix right) := by rw [hparent, hsuffix]
    _ = right := Fin.append_castAdd_natAdd

theorem prefixCylinder_parent {prefixLength block : ℕ}
    {word : Fin (prefixLength + block) → Bool × Bool} {digits : ℕ → Bool × Bool}
    (hdigits : digits ∈ prefixCylinder word) : digits ∈ prefixCylinder (wordParent word) :=
  fun position => hdigits (Fin.castAdd block position)

theorem prefixCylinder_tail {prefixLength block : ℕ}
    {word : Fin (prefixLength + block) → Bool × Bool} {digits : ℕ → Bool × Bool}
    (hdigits : digits ∈ prefixCylinder word) :
    (fun position => digits (prefixLength + position)) ∈ prefixCylinder (wordSuffix word) :=
  fun position => hdigits (Fin.natAdd prefixLength position)

/-- Children sharing a fixed parent are faithfully indexed by their block
suffixes. This is the finite counting step used after rescaling a parent. -/
theorem suffix_card_eq {prefixLength block : ℕ}
    (selected : Finset (Fin (prefixLength + block) → Bool × Bool))
    (parent : Fin prefixLength → Bool × Bool)
    (hparent : ∀ word ∈ selected, wordParent word = parent) :
    (selected.image wordSuffix).card = selected.card := by
  apply Finset.card_image_iff.2
  intro left hleft right hright hsuffix
  exact word_eq_of_parent_suffix ((hparent left hleft).trans (hparent right hright).symm) hsuffix

theorem projectedAddress_prefix_difference {ratio slope : ℝ} (hratio : 0 ≤ ratio)
    (hcontract : ratio < 1) {prefixLength : ℕ} {parent : Fin prefixLength → Bool × Bool}
    {left right : ℕ → Bool × Bool} (hleft : left ∈ prefixCylinder parent)
    (hright : right ∈ prefixCylinder parent) :
    projectedAddress ratio slope left - projectedAddress ratio slope right =
      ratio ^ prefixLength *
        (projectedAddress ratio slope (fun position => left (prefixLength + position)) -
          projectedAddress ratio slope (fun position => right (prefixLength + position))) := by
  have hprefix (coordinate : Bool × Bool → Bool) :
      prefixValue ratio (fun position => coordinate (left position)) prefixLength =
        prefixValue ratio (fun position => coordinate (right position)) prefixLength := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro position hposition
    have hsame := (hleft ⟨position, Finset.mem_range.1 hposition⟩).trans
      (hright ⟨position, Finset.mem_range.1 hposition⟩).symm
    change left position = right position at hsame
    simpa only using! congrArg (fun digit : Bool × Bool =>
      (if coordinate digit then (1 : ℝ) else 0) * ratio ^ position) hsame
  unfold projectedAddress
  rw [address_prefix_tail hratio hcontract (fun position => (left position).2) prefixLength,
    address_prefix_tail hratio hcontract (fun position => (left position).1) prefixLength,
    address_prefix_tail hratio hcontract (fun position => (right position).2) prefixLength,
    address_prefix_tail hratio hcontract (fun position => (right position).1) prefixLength,
    hprefix Prod.fst, hprefix Prod.snd]
  simp only [Nat.add_comm]
  ring

theorem rescaled_strip_of_parent {ratio slope width : ℝ} (hratio : 0 < ratio)
    (hcontract : ratio < 1) {prefixLength : ℕ} {parent : Fin prefixLength → Bool × Bool}
    {digits witness : ℕ → Bool × Bool} (hdigits : digits ∈ prefixCylinder parent)
    (hwitness : witness ∈ prefixCylinder parent)
    (hstrip : |projectedAddress ratio slope digits - projectedAddress ratio slope witness| ≤
      ratio ^ prefixLength * width) :
    |projectedAddress ratio slope (fun position => digits (prefixLength + position)) -
      projectedAddress ratio slope (fun position => witness (prefixLength + position))| ≤ width := by
  rw [projectedAddress_prefix_difference hratio.le hcontract hdigits hwitness,
    abs_mul, abs_of_pos (pow_pos hratio prefixLength)] at hstrip
  exact (mul_le_mul_iff_right₀ (pow_pos hratio prefixLength)).1 hstrip

theorem child_strip_count {ratio slope center width constant exponent : ℝ}
    (hratio : 0 < ratio) (hcontract : ratio < 1) (hwidth : 0 ≤ width)
    (hball : ∀ center radius : ℝ, 0 < radius →
      projectedMeasure ratio slope (Metric.ball center radius) ≤
        ENNReal.ofReal (constant * radius ^ exponent))
    {prefixLength block : ℕ} (selected : Finset (Fin (prefixLength + block) → Bool × Bool))
    (parent : Fin prefixLength → Bool × Bool)
    (hparent : ∀ word ∈ selected, wordParent word = parent)
    (hmeets : ∀ word ∈ selected, ∃ digits ∈ prefixCylinder word,
      |projectedAddress ratio slope (fun position => digits (prefixLength + position)) - center| ≤ width) :
    (selected.card : ℝ≥0∞) * (1 / 4 : ℝ≥0∞) ^ block ≤
      ENNReal.ofReal (constant * (width + (|slope| + 2) * ratio ^ block) ^ exponent) := by
  rw [← suffix_card_eq selected parent hparent]
  apply prefix_strip_count hratio hcontract hwidth hball
  intro suffix hsuffix
  obtain ⟨word, hword, rfl⟩ := Finset.mem_image.1 hsuffix
  obtain ⟨digits, hdigits, hstrip⟩ := hmeets word hword
  exact ⟨fun position => digits (prefixLength + position), prefixCylinder_tail hdigits, hstrip⟩

end LambdaCantor.First.PrefixSlopes

