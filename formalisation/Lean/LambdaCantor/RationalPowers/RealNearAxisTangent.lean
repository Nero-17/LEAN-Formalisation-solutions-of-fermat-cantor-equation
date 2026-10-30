import LambdaCantor.RationalPowers.RealNearAxisGeometry
import LambdaCantor.RationalPowers.RealTangent
import LambdaCantor.Integer.IrrationalTangentSelection

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

theorem real_near_axis_normalized_tangent_injective (exponent phase : ℝ) (exponent_gt_one : 1 < exponent)
    (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ)
    (phase_relation : phase = (secondDepth : ℝ)-exponent*firstDepth)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (vertical_bound : vertical+1 ≤ 3^verticalDepth) (small : (1/3 : ℝ)^secondDepth < 1)
    (drop_positive : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < realPowerDrop exponent ((1/3 : ℝ)^secondDepth) ((vertical+1-y)/3^verticalDepth)) :
    Set.InjOn (fun point : ℝ × ℝ => (exponent/(horizontal+point.1))/
      realNearAxisVertical exponent vertical ((1/3 : ℝ)^secondDepth) point.2 verticalDepth)
      (Classical.cantorLevel (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) 0) := by
  intro first first_member second second_member equality
  dsimp only at equality
  have facts (point : ℝ × ℝ) (membership : point ∈ Classical.cantorLevel
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) 0) :=
    real_near_axis_fibre_physical exponent phase horizontalDepth verticalDepth firstDepth secondDepth
      horizontal vertical phase_relation horizontal_positive vertical_positive vertical_bound small drop_positive
      point membership
  have product (point : ℝ × ℝ) (membership : point ∈ Classical.cantorLevel
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) 0) :
      ((exponent/(horizontal+point.1))/
        realNearAxisVertical exponent vertical ((1/3 : ℝ)^secondDepth) point.2 verticalDepth)*
        realFermatTangent exponent (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point) =
      (3 : ℝ)^verticalDepth*(3 : ℝ)^phase/
        ((3 : ℝ)^horizontalDepth*((1/3 : ℝ)^firstDepth)^(exponent-1)) := by
    have first_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num) membership.1.1
    have second_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num) membership.1.2
    have horizontal_real_positive : (0 : ℝ) < horizontal := by exact_mod_cast horizontal_positive
    exact real_normalized_tangent_product exponent phase (by linarith) horizontalDepth verticalDepth
      firstDepth secondDepth horizontal vertical point
      (div_pos (by linarith [first_bounds.1]) (by positivity)) (facts point membership).2.1
      (drop_positive _ second_bounds) membership.2
  have first_product := product first first_member
  have second_product := product second second_member
  have constant_nonzero : (3 : ℝ)^verticalDepth*(3 : ℝ)^phase/
      ((3 : ℝ)^horizontalDepth*((1/3 : ℝ)^firstDepth)^(exponent-1)) ≠ 0 := by positivity
  have slope_nonzero : (exponent/(horizontal+first.1))/
      realNearAxisVertical exponent vertical ((1/3 : ℝ)^secondDepth) first.2 verticalDepth ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at first_product
    exact constant_nonzero first_product.symm
  have tangent_equal : realFermatTangent exponent
        (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical first) =
      realFermatTangent exponent
        (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical second) := by
    apply mul_left_cancel₀ slope_nonzero
    rw [first_product, equality, second_product]
  apply realNearAxisPhysical_injective horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical
  apply real_fermat_tangent_injective exponent exponent_gt_one
    (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical ''
      Classical.cantorLevel (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) 0)
  · rintro point ⟨source, source_member, rfl⟩
    exact ⟨(facts source source_member).1, (facts source source_member).2.1⟩
  · rintro point ⟨source, source_member, rfl⟩
    exact (facts source source_member).2.2
  · exact ⟨first, first_member, rfl⟩
  · exact ⟨second, second_member, rfl⟩
  · exact tangent_equal

theorem real_near_axis_dimension_le_intersection (exponent phase : ℝ)
    (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ)
    (phase_relation : phase = (secondDepth : ℝ)-exponent*firstDepth)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (horizontal_prefix : ternaryPrefix horizontal horizontalDepth = true)
    (vertical_prefix : ternaryPrefix vertical verticalDepth = true)
    (vertical_bound : vertical+1 ≤ 3^verticalDepth) (small : (1/3 : ℝ)^secondDepth < 1)
    (drop_positive : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < realPowerDrop exponent ((1/3 : ℝ)^secondDepth) ((vertical+1-y)/3^verticalDepth)) :
    dimH (Classical.cantorLevel (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
      ((1/3 : ℝ)^secondDepth)) 0) ≤ dimH (intersection exponent (1/3)) := by
  obtain ⟨bound, estimate⟩ := realNearAxisPhysical_antilipschitz
    horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical
  apply (estimate.le_dimH_image _).trans (dimH_mono ?_)
  rintro point ⟨source, source_member, rfl⟩
  have membership := realNearAxisPhysical_mem_dust horizontalDepth verticalDepth firstDepth secondDepth
    horizontal vertical horizontal_prefix vertical_prefix source source_member.1
  have facts := real_near_axis_fibre_physical exponent phase horizontalDepth verticalDepth firstDepth secondDepth
    horizontal vertical phase_relation horizontal_positive vertical_positive vertical_bound small drop_positive
    source source_member
  exact ⟨membership.1, membership.2, facts.2.2⟩

end LambdaCantor.RationalPowers

