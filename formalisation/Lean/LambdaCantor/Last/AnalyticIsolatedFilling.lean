import LambdaCantor.Last.TwoBandNonlinear
import LambdaCantor.Last.TangentSource

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem coordinateGrowth_linear_add_lipschitz {error : (ℝ × ℝ) → ℝ}
    {bound : ℝ≥0} (lipschitz : LipschitzWith bound error) (slope : ℝ) :
    CoordinateGrowth (fun point => point.1+slope*point.2+error point)
      (1-(bound : ℝ)) (1+bound) (slope-bound) (slope+bound) := by
  constructor
  · intro first second height _ _ _ ordered
    have error_bound := lipschitz.dist_le_mul (second,height) (first,height)
    have error_bounds : -(bound : ℝ)*(second-first) ≤ error (second,height)-error (first,height) ∧
        error (second,height)-error (first,height) ≤ (bound : ℝ)*(second-first) := by
      simpa [Real.dist_eq, Prod.dist_eq, abs_of_nonneg (sub_nonneg.mpr ordered),
        max_eq_left (sub_nonneg.mpr ordered), max_eq_right (sub_nonneg.mpr ordered), abs_le] using error_bound
    constructor <;> dsimp <;> nlinarith [error_bounds.1, error_bounds.2]
  · intro first second width _ _ _ ordered
    have error_bound := lipschitz.dist_le_mul (width,second) (width,first)
    have error_bounds : -(bound : ℝ)*(second-first) ≤ error (width,second)-error (width,first) ∧
        error (width,second)-error (width,first) ≤ (bound : ℝ)*(second-first) := by
      simpa [Real.dist_eq, Prod.dist_eq, abs_of_nonneg (sub_nonneg.mpr ordered),
        max_eq_left (sub_nonneg.mpr ordered), max_eq_right (sub_nonneg.mpr ordered), abs_le] using error_bound
    constructor <;> dsimp <;> nlinarith [error_bounds.1, error_bounds.2]

/-- Every closed child hull is filled for a small Lipschitz perturbation of
an affine function with strict consecutive overlaps. No two-band or double
cover inequality is imposed. -/
theorem lipschitz_perturbed_word_hull_filled {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    {error : (ℝ × ℝ) → ℝ} {bound : ℝ≥0} (lipschitz : LipschitzWith bound error)
    (outer : (1-2*ratio)*(1+(bound : ℝ)) < ratio*(slope-bound))
    (middle : (1-2*ratio)*(slope+(bound : ℝ)) < 1-bound)
    (word : List (Bool × Bool)) {level : ℝ}
    (brackets : level ∈ Set.Icc
      ((fun point => point.1+slope*point.2+error point) (wordMap ratio word 0))
      ((fun point => point.1+slope*point.2+error point) (wordMap ratio word (1,1)))) :
    ∃ point ∈ wordCylinder ratio word, point.1+slope*point.2+error point = level := by
  have continuous_error : Continuous error := lipschitz.continuous
  exact nonlinear_word_closed_hull_filled (coordinateGrowth_linear_add_lipschitz lipschitz slope)
    (by fun_prop) positive less_half outer middle word brackets

end LambdaCantor.Last
