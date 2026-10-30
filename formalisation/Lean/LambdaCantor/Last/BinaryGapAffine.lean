import LambdaCantor.Last.ExternalNewhouseBinary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor.Last.ExternalNewhouse

def BinaryGapPresentation.affine {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (scale offset : ℝ) (hscale : 0 < scale) :
    BinaryGapPresentation ((fun value => scale * value + offset) '' set) where
  left := fun word => scale * presentation.left word + offset
  right := fun word => scale * presentation.right word + offset
  node_order := by
    intro word
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left (presentation.node_order word) hscale)
      (le_refl offset)
  left_coherent := by intro word; rw [presentation.left_coherent]
  right_coherent := by intro word; rw [presentation.right_coherent]
  children_order := by
    intro word
    obtain ⟨hfirst, hgap, hsecond⟩ := presentation.children_order word
    exact ⟨add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hfirst hscale) (le_refl offset),
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hgap hscale) (le_refl offset),
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hsecond hscale) (le_refl offset)⟩
  limit_set := by
    ext point
    constructor
    · rintro ⟨original, hmem, rfl⟩ depth
      rw [presentation.limit_set] at hmem
      obtain ⟨word, hlength, hbounds⟩ := hmem depth
      exact ⟨word, hlength,
        add_le_add (mul_le_mul_of_nonneg_left hbounds.1 hscale.le) (le_refl offset),
        add_le_add (mul_le_mul_of_nonneg_left hbounds.2 hscale.le) (le_refl offset)⟩
    · intro hpoint
      refine ⟨(point - offset) / scale, ?_, ?_⟩
      · rw [presentation.limit_set]
        intro depth
        obtain ⟨word, hlength, hbounds⟩ := hpoint depth
        refine ⟨word, hlength, ?_, ?_⟩
        · apply (le_div_iff₀ hscale).mpr
          nlinarith [hbounds.1]
        · apply (div_le_iff₀ hscale).mpr
          nlinarith [hbounds.2]
      · field_simp [hscale.ne']
        <;> ring
  mesh := by
    intro epsilon hepsilon
    obtain ⟨depth, hdepth⟩ := presentation.mesh (epsilon / scale) (div_pos hepsilon hscale)
    refine ⟨depth, ?_⟩
    intro word hword
    have hbound := mul_lt_mul_of_pos_left (hdepth word hword) hscale
    have hcancel : scale * (epsilon / scale) = epsilon := by
      field_simp [hscale.ne']
    nlinarith

theorem BinaryGapPresentation.affine_bridgeBound {set : Set ℝ}
    (presentation : BinaryGapPresentation set) {bound scale offset : ℝ}
    (hscale : 0 < scale) (hbound : presentation.bridgeBound bound) :
    (presentation.affine scale offset hscale).bridgeBound bound := by
  intro word
  obtain ⟨hleft, hright⟩ := hbound word
  constructor
  · change bound * ((scale * presentation.left (word ++ [true]) + offset) -
        (scale * presentation.right (word ++ [false]) + offset)) ≤
      (scale * presentation.right (word ++ [false]) + offset) -
        (scale * presentation.left word + offset)
    calc
      bound * ((scale * presentation.left (word ++ [true]) + offset) -
          (scale * presentation.right (word ++ [false]) + offset)) =
          scale * (bound * (presentation.left (word ++ [true]) -
            presentation.right (word ++ [false]))) := by ring
      _ ≤ scale * (presentation.right (word ++ [false]) - presentation.left word) :=
        mul_le_mul_of_nonneg_left hleft hscale.le
      _ = (scale * presentation.right (word ++ [false]) + offset) -
          (scale * presentation.left word + offset) := by ring
  · change bound * ((scale * presentation.left (word ++ [true]) + offset) -
        (scale * presentation.right (word ++ [false]) + offset)) ≤
      (scale * presentation.right word + offset) -
        (scale * presentation.left (word ++ [true]) + offset)
    calc
      bound * ((scale * presentation.left (word ++ [true]) + offset) -
          (scale * presentation.right (word ++ [false]) + offset)) =
          scale * (bound * (presentation.left (word ++ [true]) -
            presentation.right (word ++ [false]))) := by ring
      _ ≤ scale * (presentation.right word - presentation.left (word ++ [true])) :=
        mul_le_mul_of_nonneg_left hright hscale.le
      _ = (scale * presentation.right word + offset) -
          (scale * presentation.left (word ++ [true]) + offset) := by ring

end LambdaCantor.Last.ExternalNewhouse
