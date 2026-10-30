import LambdaCantor.Classical.GeneralCoverLocal
import LambdaCantor.Integer.AffineCoverage

namespace LambdaCantor.Integer

theorem affine_coordinate_bounds (r : ℝ) :
    Classical.CoordinateBounds (fun x y : ℝ => (r*x+y)/2) (r/2) (r/2) (1/2) (1/2) := by
  constructor
  · intro y hy first hfirst second hsecond ordered
    constructor <;> nlinarith
  · intro x hx first hfirst second hsecond ordered
    constructor <;> nlinarith

/-- Full affine Cantor image, obtained from the general finite-stage coverage
and compact intersection theorem rather than from an assumed sumset theorem. -/
theorem affine_cantor_image (r : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3) :
    (fun point : ℝ × ℝ => (r*point.1+point.2)/2) ''
      (_root_.cantorSet ×ˢ _root_.cantorSet) = Set.Icc 0 ((r+1)/2) := by
  have continuous : Continuous (fun point : ℝ × ℝ => (r*point.1+point.2)/2) :=
    ((continuous_const.mul continuous_fst).add continuous_snd).div_const 2
  have image := Classical.general_cantor_image (fun x y : ℝ => (r*x+y)/2)
    continuous.continuousOn (r/2) (r/2) (1/2) (1/2) (affine_coordinate_bounds r)
    (by linarith) (by norm_num) (by linarith) (by linarith)
    0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [zero_add, one_mul, mul_zero, add_zero, zero_div, mul_one] using image

theorem affine_fibre_nonempty (r u : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (level : u ∈ Set.Icc 0 ((r+1)/2)) :
    ∃ first ∈ _root_.cantorSet, ∃ second ∈ _root_.cantorSet,
      (r*first+second)/2=u := by
  rw [← affine_cantor_image r lower upper] at level
  obtain ⟨⟨first, second⟩, ⟨firstMember, secondMember⟩, value⟩ := level
  exact ⟨first, firstMember, second, secondMember, value⟩

end LambdaCantor.Integer
