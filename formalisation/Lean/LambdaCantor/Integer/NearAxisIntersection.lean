import LambdaCantor.Integer.NearAxisTangent
import LambdaCantor.Integer.NearAxisCylinders

namespace LambdaCantor.Integer

/-- The exact normalized level set maps into the manuscript's intersection,
including its address-defined Cantor sets and real-power convention. -/
theorem near_axis_image_subset_intersection (n d p q k P Q : ℕ)
    (positiveP : 0 < P) (positiveQ : 0 < Q) (boundQ : Q+1 ≤ 3^q)
    (prefixP : ternaryPrefix P p = true) (prefixQ : ternaryPrefix Q q = true)
    (small : (1/3 : ℝ)^(n*k+d) < 1)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q))) :
    nearAxisPhysical n d p q k P Q '' Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0 ⊆
        intersection (n : ℝ) (1/3) := by
  rintro _ ⟨point,member,rfl⟩
  have firstMember : point.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.1
  have secondMember : point.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.2
  have cylinders := near_axis_physical_cylinders n d k P Q p q prefixP prefixQ
    point.1 point.2 firstMember secondMember
  have equation := (near_axis_fibre_physical n d p q k P Q positiveP positiveQ
    boundQ small positiveResidual point member).2.2
  refine ⟨?_,?_,?_⟩
  · rw [cantorSet_third_eq]
    exact cylinders.1
  · rw [cantorSet_third_eq]
    exact cylinders.2
  · simpa only [Real.rpow_natCast] using equation

theorem continuous_nearAxisPhysical (n d p q k P Q : ℕ) :
    Continuous (nearAxisPhysical n d p q k P Q) :=
  (continuous_const.mul ((continuous_const.add continuous_fst).div_const _)).prodMk
    (continuous_const.sub (continuous_const.mul
      ((continuous_const.sub continuous_snd).div_const _)))

end LambdaCantor.Integer
