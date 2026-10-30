import LambdaCantor.Last.StrictReturnDimension

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last
namespace FiniteReturnAtlas

/-- Use an explicitly bounded certificate atlas with an error defined only on
the actual Cantor dust; the supplied depth and margin are retained. -/
theorem positive_dimension_on_dust
    {ratio : ℝ} {linear : (ℝ × ℝ) →ₗ[ℝ] ℝ} {levels : Set ℝ}
    (atlas : FiniteReturnAtlas ratio linear levels)
    (hpositive : 0 < ratio) (hless : ratio < 1 / 2) (bound : ℝ≥0)
    (hsmall : (bound : ℝ) < atlas.margin * ratio ^ atlas.maxDepth)
    (linearBound levelBound : ℝ) (hlinearBound : 0 ≤ linearBound) (hlevelBound : 0 ≤ levelBound)
    (hlinear : ∀ point ∈ cantorDust ratio, |linear point| ≤ linearBound)
    (hlevels : ∀ level ∈ levels, |level| ≤ levelBound)
    (error : (ℝ × ℝ) → ℝ) (hlipschitz : LipschitzOnWith bound error (cantorDust ratio))
    (hzero : error 0 = 0) (level : ℝ) (hlevel : level ∈ levels) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ linear point + error point = level} := by
  obtain ⟨extension, hextension, hagreement⟩ := hlipschitz.extend_real
  have hextension_zero : extension 0 = 0 := by
    rw [← hagreement ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩]
    exact hzero
  have hdimension := atlas.positive_dimension hpositive hless bound hsmall
    linearBound levelBound hlinearBound hlevelBound hlinear hlevels
    ⟨level, hlevel, extension, hextension_zero, hextension⟩
  apply hdimension.trans_le (dimH_mono ?_)
  intro point hpoint
  refine ⟨hpoint.1, ?_⟩
  have hequation : linear point + extension point = level := hpoint.2
  rw [hagreement hpoint.1]
  exact hequation

/-- The certificate terminal for an actual nonlinear function. The level is
shifted by the original corner value, so no corner-zero hypothesis is needed. -/
theorem positive_dimension_actual_fibre
    {ratio : ℝ} {linear : (ℝ × ℝ) →ₗ[ℝ] ℝ} {levels : Set ℝ}
    (atlas : FiniteReturnAtlas ratio linear levels)
    (hpositive : 0 < ratio) (hless : ratio < 1 / 2) (bound : ℝ≥0)
    (hsmall : (bound : ℝ) < atlas.margin * ratio ^ atlas.maxDepth)
    (linearBound levelBound : ℝ) (hlinearBound : 0 ≤ linearBound) (hlevelBound : 0 ≤ levelBound)
    (hlinear : ∀ point ∈ cantorDust ratio, |linear point| ≤ linearBound)
    (hlevels : ∀ level ∈ levels, |level| ≤ levelBound)
    (function : (ℝ × ℝ) → ℝ)
    (hlipschitz : LipschitzOnWith bound
      (fun point => function point - function 0 - linear point) (cantorDust ratio))
    (level : ℝ) (hlevel : level - function 0 ∈ levels) :
    0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point = level} := by
  have hdimension := atlas.positive_dimension_on_dust hpositive hless bound hsmall
    linearBound levelBound hlinearBound hlevelBound hlinear hlevels
    (fun point => function point - function 0 - linear point) hlipschitz
    (by simp) (level - function 0) hlevel
  apply hdimension.trans_le (dimH_mono ?_)
  intro point hpoint
  refine ⟨hpoint.1, ?_⟩
  linarith [hpoint.2]

end FiniteReturnAtlas
end LambdaCantor.Last
