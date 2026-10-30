import LambdaCantor.Classical.Cover

noncomputable section
namespace LambdaCantor.Classical

lemma cantor_prepend_zero {point : ℝ} (membership : point ∈ _root_.cantorSet) :
    point / 3 ∈ _root_.cantorSet := by
  rw [cantorSet_eq_union_halves]
  exact Or.inl ⟨point, membership, rfl⟩

lemma cantor_prepend_two {point : ℝ} (membership : point ∈ _root_.cantorSet) :
    (2 + point) / 3 ∈ _root_.cantorSet := by
  rw [cantorSet_eq_union_halves]
  exact Or.inr ⟨point, membership, rfl⟩

theorem source_x_mem_cantor {point : ℝ} (membership : point ∈ cantorSet (1 / 3)) :
    (566 + point) / 3 ^ 7 ∈ cantorSet (1 / 3) := by
  rw [cantorSet_third_eq] at membership ⊢
  convert cantor_prepend_zero (cantor_prepend_two (cantor_prepend_zero
    (cantor_prepend_two (cantor_prepend_two (cantor_prepend_two
      (cantor_prepend_two membership)))))) using 1 <;> ring

theorem source_y_mem_cantor {point : ℝ} (membership : point ∈ cantorSet (1 / 3)) :
    (6336 + point) / 3 ^ 8 ∈ cantorSet (1 / 3) := by
  rw [cantorSet_third_eq] at membership ⊢
  convert cantor_prepend_two (cantor_prepend_two (cantor_prepend_two
    (cantor_prepend_zero (cantor_prepend_zero (cantor_prepend_two
      (cantor_prepend_zero (cantor_prepend_zero membership))))))) using 1 <;> ring

def sourceLevel : Set (ℝ × ℝ) :=
  (cantorSet (1 / 3) ×ˢ cantorSet (1 / 3)) ∩
    (fun point => cylinderPolynomial point.1 point.2) ⁻¹' {3 ^ 16}

def source : Set (ℝ × ℝ) := cylinderMap '' sourceLevel

theorem sourceLevel_nonempty : sourceLevel.Nonempty := by
  obtain ⟨first, second, first_member, second_member, value⟩ := source_level_nonempty
  exact ⟨(first, second), ⟨first_member, second_member⟩, value⟩

theorem source_nonempty : source.Nonempty := sourceLevel_nonempty.image cylinderMap

theorem sourceLevel_compact : IsCompact sourceLevel := by
  have continuous_polynomial : Continuous (fun point : ℝ × ℝ =>
      cylinderPolynomial point.1 point.2) := by unfold cylinderPolynomial; fun_prop
  exact ((LambdaCantor.isCompact_cantorSet (by norm_num) (by norm_num)).prod
    (LambdaCantor.isCompact_cantorSet (by norm_num) (by norm_num))).inter_right
      (isClosed_singleton.preimage continuous_polynomial)

theorem source_compact : IsCompact source := sourceLevel_compact.image cylinderMap_continuous

theorem source_subset_circle : source ⊆ intersection 2 (1 / 3) := by
  rintro point ⟨preimage, membership, rfl⟩
  refine ⟨source_x_mem_cantor membership.1.2, source_y_mem_cantor membership.1.1, ?_⟩
  have equation := (cylinder_circle_iff preimage.1 preimage.2).mpr membership.2
  simpa only [cylinderMap, Real.rpow_two] using equation

end LambdaCantor.Classical
