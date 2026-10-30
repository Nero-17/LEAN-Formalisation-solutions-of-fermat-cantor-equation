import LambdaCantor.AE.CenteredPrefixWindow
import LambdaCantor.AE.CenteredSmallBallActual
import LambdaCantor.AE.FreezingAverageOverlapReal

noncomputable section
open Set MeasureTheory
namespace LambdaCantor.AE
open First.PrefixSlopes

def centeredPrefixRepresentative (depth : ℕ) (word : Fin depth → Bool × Bool) : ℕ → Bool × Bool :=
  fun index => if before : index < depth then word ⟨index, before⟩ else (false, false)

/-- Canonical root centres are actual roots of fixed extensions of each prefix. -/
theorem centered_prefix_root_interval
    (root : (ℕ → Bool × Bool) → ℝ) (depth : ℕ) {radius : ℝ}
    (prefix_displacement : ∀ first second : ℕ → Bool × Bool,
      (∀ position < depth, first position = second position) → |root first-root second| ≤ radius) :
    ∀ word digits, digits ∈ prefixCylinder word →
      root digits ∈ Icc (root (centeredPrefixRepresentative depth word)-radius)
        (root (centeredPrefixRepresentative depth word)+radius) := by
  intro word digits digits_mem
  have displacement := prefix_displacement digits (centeredPrefixRepresentative depth word)
    (by intro position before; simpa [centeredPrefixRepresentative, before] using digits_mem ⟨position, before⟩)
  have bounds := abs_le.mp displacement
  constructor <;> linarith [bounds.1, bounds.2]

/-- Exact freezing overlap scale. All constants displayed here are independent
of the tail depth and of rho once the uniform centered estimates are supplied. -/
theorem centered_root_freezing_overlap
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    (depth : ℕ) {rho upper dimension displacementConstant smallBallConstant : ℝ}
    (rho_positive : 0 < rho) (upper_positive : 0 < upper)
    (displacement_positive : 0 < displacementConstant) (smallBall_nonnegative : 0 ≤ smallBallConstant)
    (prefix_displacement : ∀ first second : ℕ → Bool × Bool,
      (∀ position < depth, first position = second position) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (small_ball : ∀ left right : ℝ, left ≤ right →
      First.Roots.rootLaw root (Icc left right) ≤
        ENNReal.ofReal (smallBallConstant*((right-left)/rho)^dimension)) :
    ∀ point : ℝ, (∑ word : Fin depth → Bool × Bool,
      (Icc (root (centeredPrefixRepresentative depth word)-displacementConstant*rho*upper^depth)
        (root (centeredPrefixRepresentative depth word)+displacementConstant*rho*upper^depth)).indicator
          (fun _ => (1/4:ℝ)^depth) point) ≤
      (smallBallConstant*(4*displacementConstant)^dimension)*upper^((depth:ℝ)*dimension) := by
  intro point
  apply root_prefix_indicator_overlap root root_measurable depth
    (fun word => root (centeredPrefixRepresentative depth word)) (by positivity)
    (centered_prefix_root_interval root depth prefix_displacement)
  have radius_positive : 0 < displacementConstant*rho*upper^depth := by positivity
  have bound := small_ball (point-2*(displacementConstant*rho*upper^depth))
    (point+2*(displacementConstant*rho*upper^depth)) (by linarith)
  have width_identity :
      ((point+2*(displacementConstant*rho*upper^depth))-(point-2*(displacementConstant*rho*upper^depth)))/rho =
        (4*displacementConstant)*upper^depth := by field_simp [rho_positive.ne']; ring
  rw [width_identity, Real.mul_rpow (by positivity) (pow_nonneg upper_positive.le depth),
    ← Real.rpow_natCast_mul upper_positive.le] at bound
  simpa only [mul_assoc] using bound

end LambdaCantor.AE
