import LambdaCantor.First.FrostmanNull
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
namespace LambdaCantor.First

open Set MeasureTheory
open scoped ENNReal NNReal

/-- A ball centered outside the image is controlled by a ball of twice the
radius centered at any image point that it contains. -/
theorem map_ball_bound_of_image_ball_bound {Source X : Type*}
    [MeasurableSpace Source] [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure Source) {map : Source → X} (hmeasurable : Measurable map)
    {constant exponent cutoff : ℝ}
    (hball : ∀ point : Source, ∀ radius : ℝ, 0 < radius → radius < cutoff →
      measure (map ⁻¹' Metric.ball (map point) radius) ≤
        ENNReal.ofReal (constant * radius ^ exponent))
    (center : X) {radius : ℝ} (hradius : 0 < radius) (hsmall : 2 * radius < cutoff) :
    measure.map map (Metric.ball center radius) ≤
      ENNReal.ofReal (constant * (2 * radius) ^ exponent) := by
  rw [Measure.map_apply hmeasurable Metric.isOpen_ball.measurableSet]
  rcases (map ⁻¹' Metric.ball center radius).eq_empty_or_nonempty with hempty | ⟨point, hpoint⟩
  · simp [hempty]
  apply (measure_mono (show map ⁻¹' Metric.ball center radius ⊆
      map ⁻¹' Metric.ball (map point) (2 * radius) from ?_)).trans
    (hball point (2 * radius) (by positivity) hsmall)
  intro other hother
  change dist (map other) (map point) < 2 * radius
  have hfirst : dist (map other) center < radius := hother
  have hsecond : dist center (map point) < radius := by
    have hpointDistance : dist (map point) center < radius := hpoint
    simpa only [dist_comm] using hpointDistance
  exact (dist_triangle _ _ _).trans_lt (by linarith)

/-- Local ball control stated in real radii implies the extended-radius form
used by Hausdorff measure. -/
theorem extended_ball_bound_of_real_ball_bound {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] (measure : Measure X)
    (exponent : ℝ≥0) {constant cutoff : ℝ} (hconstant : 0 ≤ constant)
    (hball : ∀ center : X, ∀ radius : ℝ, 0 < radius → radius < cutoff →
      measure (Metric.ball center radius) ≤ ENNReal.ofReal (constant * radius ^ (exponent : ℝ)))
    (center : X) {radius : ℝ≥0∞} (hradius : 0 < radius)
    (hsmall : radius < ENNReal.ofReal cutoff) :
    measure (EMetric.ball center radius) ≤ ENNReal.ofReal constant * radius ^ (exponent : ℝ) := by
  have hfinite : radius ≠ ∞ := (hsmall.trans ENNReal.ofReal_lt_top).ne
  have hrealpositive : 0 < radius.toReal := ENNReal.toReal_pos hradius.ne' hfinite
  have hrealradius : radius.toReal < cutoff :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).1
      (by simpa only [ENNReal.ofReal_toReal hfinite] using hsmall)
  have h := hball center radius.toReal hrealpositive hrealradius
  have hballEq : EMetric.ball center radius = Metric.ball center radius.toReal := by
    rw [← Metric.eball_ofReal, ENNReal.ofReal_toReal hfinite]
    rfl
  have hpower : ENNReal.ofReal (radius.toReal ^ (exponent : ℝ)) = radius ^ (exponent : ℝ) := by
    calc
      _ = ENNReal.ofReal radius.toReal ^ (exponent : ℝ) :=
        (ENNReal.ofReal_rpow_of_pos hrealpositive).symm
      _ = radius ^ (exponent : ℝ) :=
        congrArg (fun value : ℝ≥0∞ => value ^ (exponent : ℝ))
          (ENNReal.ofReal_toReal hfinite)
  rw [hballEq]
  calc
    _ ≤ ENNReal.ofReal (constant * radius.toReal ^ (exponent : ℝ)) := h
    _ = ENNReal.ofReal constant * radius ^ (exponent : ℝ) := by
      rw [ENNReal.ofReal_mul hconstant, hpower]

/-- The image-centered Frostman hypothesis suffices to exclude all
one-dimensional exceptional sets from the pushforward law. -/
theorem map_null_of_image_ball_bound {Source X : Type*}
    [MeasurableSpace Source] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (measure : Measure Source) {map : Source → X} (hmeasurable : Measurable map)
    (exponent : ℝ≥0) (hexponent : 1 < exponent)
    {constant cutoff : ℝ} (hconstant : 0 < constant) (hcutoff : 0 < cutoff)
    (hball : ∀ point : Source, ∀ radius : ℝ, 0 < radius → radius < cutoff →
      measure (map ⁻¹' Metric.ball (map point) radius) ≤
        ENNReal.ofReal (constant * radius ^ (exponent : ℝ)))
    {exceptional : Set X} (hdimension : dimH exceptional ≤ 1) :
    measure.map map exceptional = 0 := by
  have hreal : ∀ center : X, ∀ radius : ℝ, 0 < radius → radius < cutoff / 2 →
      measure.map map (Metric.ball center radius) ≤
        ENNReal.ofReal ((constant * 2 ^ (exponent : ℝ)) * radius ^ (exponent : ℝ)) := by
    intro center radius hradius hsmall
    have h := map_ball_bound_of_image_ball_bound measure hmeasurable hball center
      hradius (by linarith)
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hradius.le, mul_assoc] using h
  apply measure_zero_of_dimH_le_one_of_ball_bound (measure.map map) exponent hexponent
    (constant := ENNReal.ofReal (constant * 2 ^ (exponent : ℝ)))
    (cutoff := ENNReal.ofReal (cutoff / 2)) (smallCutoff := ENNReal.ofReal (cutoff / 4))
  · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_pos.mpr (by positivity)
  · exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  · intro center radius hradius hsmall
    exact extended_ball_bound_of_real_ball_bound (measure.map map) exponent
      (by positivity) hreal center hradius hsmall
  · exact hdimension

end LambdaCantor.First
