import LambdaCantor.Integer.NearAxisIntersection
import Mathlib.Analysis.Normed.Ring.Lemmas

namespace LambdaCantor.Integer

theorem diagonal_affine_antilipschitz (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    AntilipschitzWith (‖a‖₊⁻¹+‖c‖₊⁻¹)
      (fun point : ℝ × ℝ => (a*point.1+b,c*point.2+d)) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro first second
  rw [Prod.dist_eq]
  apply max_le
  · calc
      dist first.1 second.1 ≤ (‖a‖₊⁻¹ : ℝ)*dist (a*first.1) (a*second.1) :=
        (antilipschitzWith_mul_left ha).le_mul_dist _ _
      _ ≤ (‖a‖₊⁻¹ : ℝ)*dist (a*first.1+b,c*first.2+d)
          (a*second.1+b,c*second.2+d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Prod.dist_eq,dist_add_right] using
          (le_max_left (dist (a*first.1) (a*second.1)) (dist (c*first.2) (c*second.2)))
      _ ≤ ↑(‖a‖₊⁻¹+‖c‖₊⁻¹)*dist (a*first.1+b,c*first.2+d)
          (a*second.1+b,c*second.2+d) := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        simp only [NNReal.coe_add]
        exact le_add_of_nonneg_right (by positivity)
  · calc
      dist first.2 second.2 ≤ (‖c‖₊⁻¹ : ℝ)*dist (c*first.2) (c*second.2) :=
        (antilipschitzWith_mul_left hc).le_mul_dist _ _
      _ ≤ (‖c‖₊⁻¹ : ℝ)*dist (a*first.1+b,c*first.2+d)
          (a*second.1+b,c*second.2+d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Prod.dist_eq,dist_add_right] using
          (le_max_right (dist (a*first.1) (a*second.1)) (dist (c*first.2) (c*second.2)))
      _ ≤ ↑(‖a‖₊⁻¹+‖c‖₊⁻¹)*dist (a*first.1+b,c*first.2+d)
          (a*second.1+b,c*second.2+d) := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        simp only [NNReal.coe_add]
        exact le_add_of_nonneg_left (by positivity)

theorem nearAxisPhysical_antilipschitz (n d p q k P Q : ℕ) :
    AntilipschitzWith
      (‖(1/3 : ℝ)^k/3^p‖₊⁻¹+‖(1/3 : ℝ)^(n*k+d)/3^q‖₊⁻¹)
      (nearAxisPhysical n d p q k P Q) := by
  have identity : nearAxisPhysical n d p q k P Q =
      (fun point : ℝ × ℝ =>
        (((1/3 : ℝ)^k/3^p)*point.1+((1/3 : ℝ)^k/3^p)*P,
          ((1/3 : ℝ)^(n*k+d)/3^q)*point.2+
            (1-((1/3 : ℝ)^(n*k+d)/3^q)*(Q+1)))) := by
    funext point
    apply Prod.ext <;> dsimp [nearAxisPhysical] <;> ring
  rw [identity]
  exact diagonal_affine_antilipschitz _ _ _ _ (by positivity) (by positivity)

theorem near_axis_dimension_le_intersection (n d p q k P Q : ℕ)
    (positiveP : 0 < P) (positiveQ : 0 < Q) (boundQ : Q+1 ≤ 3^q)
    (prefixP : ternaryPrefix P p = true) (prefixQ : ternaryPrefix Q q = true)
    (small : (1/3 : ℝ)^(n*k+d) < 1)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q))) :
    dimH (Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0) ≤
      dimH (intersection (n : ℝ) (1/3)) :=
  ((nearAxisPhysical_antilipschitz n d p q k P Q).le_dimH_image _).trans
    (dimH_mono (near_axis_image_subset_intersection n d p q k P Q positiveP positiveQ
      boundQ prefixP prefixQ small positiveResidual))

end LambdaCantor.Integer

