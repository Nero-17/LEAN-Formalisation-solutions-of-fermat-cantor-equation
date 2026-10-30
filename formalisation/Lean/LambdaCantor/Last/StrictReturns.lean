import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

/-- Affine restriction to a square of side `scale` and lower corner `corner`. -/
def restrictPoint (scale : ℝ) (corner point : ℝ × ℝ) : ℝ × ℝ :=
  corner + scale • point

/-- The new level after restriction and subtraction of the constant error. -/
def returnLevel (scale level cornerValue : ℝ) : ℝ :=
  (level - cornerValue) / scale

/-- The normalized error retains zero constant term. -/
def normalizedError (error : (ℝ × ℝ) → ℝ) (scale : ℝ)
    (corner point : ℝ × ℝ) : ℝ :=
  (error (restrictPoint scale corner point) - error corner) / scale

@[simp] theorem normalizedError_zero (error : (ℝ × ℝ) → ℝ)
    (scale : ℝ) (corner : ℝ × ℝ) :
    normalizedError error scale corner 0 = 0 := by
  simp [normalizedError, restrictPoint]

/-- Exact identity behind the recursive strict-return construction. -/
theorem restriction_identity (linear : (ℝ × ℝ) →ₗ[ℝ] ℝ)
    (error : (ℝ × ℝ) → ℝ) (scale level : ℝ) (hscale : scale ≠ 0)
    (corner point : ℝ × ℝ) :
    linear (restrictPoint scale corner point) +
        error (restrictPoint scale corner point) - level =
      scale * (linear point + normalizedError error scale corner point -
        returnLevel scale level (linear corner + error corner)) := by
  simp only [restrictPoint, map_add, map_smul, smul_eq_mul,
    normalizedError, returnLevel]
  field_simp
  <;> ring

/-- A level perturbation smaller than the available margin remains in the interval. -/
theorem returnLevel_mem_Ioo_of_margin
    (scale level cornerValue errorValue lower upper margin : ℝ)
    (hscale : 0 < scale) (hmargin : 0 < margin)
    (hlower : lower + margin ≤ returnLevel scale level cornerValue)
    (hupper : returnLevel scale level cornerValue ≤ upper - margin)
    (herror : |errorValue| < margin * scale) :
    returnLevel scale level (cornerValue + errorValue) ∈ Set.Ioo lower upper := by
  have herror' : |errorValue / scale| < margin := by
    rw [abs_div, abs_of_pos hscale, div_lt_iff₀ hscale]
    exact herror
  have hid : returnLevel scale level (cornerValue + errorValue) =
      returnLevel scale level cornerValue - errorValue / scale := by
    simp only [returnLevel]
    ring
  rw [hid]
  rcases abs_lt.mp herror' with ⟨hneg, hpos⟩
  constructor <;> linarith

/-- Uniform positive margin handles every chosen cylinder of depth at most `maxDepth`. -/
theorem error_lt_margin_mul_scale
    (ratio margin errorBound errorValue : ℝ) (depth maxDepth : ℕ)
    (hratio : 0 < ratio) (hratio_one : ratio ≤ 1) (hdepth : depth ≤ maxDepth)
    (hmargin : 0 < margin) (herrorBound : errorBound < margin * ratio ^ maxDepth)
    (herror : |errorValue| ≤ errorBound) :
    |errorValue| < margin * ratio ^ depth := by
  have hpow : ratio ^ maxDepth ≤ ratio ^ depth :=
    pow_le_pow_of_le_one (le_of_lt hratio) hratio_one hdepth
  exact herror.trans_lt (herrorBound.trans_le (mul_le_mul_of_nonneg_left hpow hmargin.le))

/-- The rescaling used at every return does not increase the Lipschitz constant. -/
theorem normalizedError_lipschitz {error : (ℝ × ℝ) → ℝ} {bound : ℝ≥0}
    (hlipschitz : LipschitzWith bound error) (scale : ℝ) (hscale : 0 < scale)
    (corner : ℝ × ℝ) : LipschitzWith bound (normalizedError error scale corner) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hbound := hlipschitz.dist_le_mul (restrictPoint scale corner first)
    (restrictPoint scale corner second)
  rw [restrictPoint, restrictPoint, dist_add_left, dist_smul₀,
    Real.norm_eq_abs, abs_of_pos hscale, Real.dist_eq] at hbound
  rw [Real.dist_eq]
  have hdifference : normalizedError error scale corner first -
      normalizedError error scale corner second =
      (error (restrictPoint scale corner first) - error (restrictPoint scale corner second)) / scale := by
    unfold normalizedError
    ring
  rw [hdifference, abs_div, abs_of_pos hscale, div_le_iff₀ hscale]
  dsimp only [restrictPoint]
  nlinarith [hbound]

end LambdaCantor.Last
