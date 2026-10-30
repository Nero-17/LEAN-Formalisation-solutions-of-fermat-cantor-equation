import LambdaCantor.Common
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# External homogeneous projection input

The only axiom in this module is the equal-four-weight specialization of
Pablo Shmerkin, "On Furstenberg's intersection conjecture, self-similar
measures, and the L^q norms of convolutions", Annals of Mathematics 189
(2019), Theorem 6.2, printed page 368.
Primary source: https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n2-p01-s.pdf

The hypotheses describe an actual invariant probability law of four affine
contractions, with injective translations and separation of distinct words
at infinitely many levels. They do not assume a strip count or dimension
conclusion. Equal distinct weights give ||Delta||_infinity = 1/4, so the
theorem's exponent log||Delta||_infinity/log(ratio) is log4/log(1/ratio).
The extension from small radii to all positive radii below is proved here.
-/

noncomputable section
namespace LambdaCantor.First.ExternalProjection

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- Translation of a finite composition, with words listed from outermost
map to innermost map. -/
def wordTranslation (ratio : ℝ) (translation : Fin 4 → ℝ) {depth : ℕ}
    (word : Fin depth → Fin 4) : ℝ :=
  ∑ position : Fin depth, ratio ^ (position : ℕ) * translation (word position)

/-- Uniform exponential separation of all distinct words at infinitely many
depths. Exact overlaps therefore violate this condition. -/
def HasExponentialSeparation (ratio : ℝ) (translation : Fin 4 → ℝ) : Prop :=
  ∃ separation : ℝ, 0 < separation ∧
    ∃ᶠ depth : ℕ in atTop,
      ∀ left right : Fin depth → Fin 4, left ≠ right →
        separation ^ depth ≤
          |wordTranslation ratio translation left - wordTranslation ratio translation right|

/-- The fixed-point equation for the homogeneous self-similar probability
whose four affine maps have equal weights. -/
def IsFourMapInvariant (measure : Measure ℝ) (ratio : ℝ)
    (translation : Fin 4 → ℝ) : Prop :=
  measure = ∑ index : Fin 4, (4 : ℝ≥0∞)⁻¹ •
    Measure.map (fun point : ℝ => ratio * point + translation index) measure

/-- Established external theorem: Shmerkin 2019, Theorem 6.2, specialized to
four distinct equal-weight maps. This is the sole unproved external input;
no result internal to the frozen manuscript is axiomatized. -/
axiom shmerkin2019_theorem62_four_maps
    (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (ratio : ℝ) (translation : Fin 4 → ℝ)
    (hratio : 0 < ratio) (hcontract : ratio < 1)
    (hdistinct : Function.Injective translation)
    (hinvariant : IsFourMapInvariant measure ratio translation)
    (hseparation : HasExponentialSeparation ratio translation)
    (exponent : ℝ) (hpositive : 0 < exponent)
    (hexponent : exponent < min (Real.log 4 / Real.log (1 / ratio)) 1) :
    ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ center radius : ℝ, 0 < radius → radius < cutoff →
        measure (Metric.ball center radius) ≤ ENNReal.ofReal (radius ^ exponent)

/-- A small-radius power bound for a probability measure extends to all
positive radii, with a constant independent of the center and radius. -/
theorem global_ball_bound_of_small_radius_bound (measure : Measure ℝ)
    [IsProbabilityMeasure measure] {exponent cutoff : ℝ}
    (hexponent : 0 ≤ exponent) (hcutoff : 0 < cutoff)
    (hsmall : ∀ center radius : ℝ, 0 < radius → radius < cutoff →
      measure (Metric.ball center radius) ≤ ENNReal.ofReal (radius ^ exponent)) :
    ∀ center radius : ℝ, 0 < radius →
      measure (Metric.ball center radius) ≤
        ENNReal.ofReal (max 1 (cutoff ^ exponent)⁻¹ * radius ^ exponent) := by
  intro center radius hradius
  have hpower : 0 < cutoff ^ exponent := Real.rpow_pos_of_pos hcutoff _
  by_cases hnear : radius < cutoff
  · apply (hsmall center radius hradius hnear).trans
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right
      (le_max_left (1 : ℝ) (cutoff ^ exponent)⁻¹)
      (Real.rpow_nonneg hradius.le exponent)
    simpa only [one_mul] using h
  · apply (prob_le_one (μ := measure)).trans
    apply ENNReal.one_le_ofReal.2
    calc
      1 = (cutoff ^ exponent)⁻¹ * cutoff ^ exponent :=
        (inv_mul_cancel₀ (ne_of_gt hpower)).symm
      _ ≤ max 1 (cutoff ^ exponent)⁻¹ * cutoff ^ exponent :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hpower.le
      _ ≤ max 1 (cutoff ^ exponent)⁻¹ * radius ^ exponent :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hcutoff.le (le_of_not_gt hnear) hexponent)
          (le_trans zero_le_one (le_max_left _ _))

/-- Usable all-scale projection estimate. The only external dependency is
the exact homogeneous probability theorem above. -/
theorem shmerkin_four_map_global_ball_bound
    (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (ratio : ℝ) (translation : Fin 4 → ℝ)
    (hratio : 0 < ratio) (hcontract : ratio < 1)
    (hdistinct : Function.Injective translation)
    (hinvariant : IsFourMapInvariant measure ratio translation)
    (hseparation : HasExponentialSeparation ratio translation)
    (exponent : ℝ) (hpositive : 0 < exponent)
    (hexponent : exponent < min (Real.log 4 / Real.log (1 / ratio)) 1) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ center radius : ℝ, 0 < radius →
      measure (Metric.ball center radius) ≤ ENNReal.ofReal (constant * radius ^ exponent) := by
  obtain ⟨cutoff, hcutoff, hsmall⟩ := shmerkin2019_theorem62_four_maps measure ratio translation
    hratio hcontract hdistinct hinvariant hseparation exponent hpositive hexponent
  refine ⟨max 1 (cutoff ^ exponent)⁻¹,
    zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  exact global_ball_bound_of_small_radius_bound measure hpositive.le hcutoff hsmall

end LambdaCantor.First.ExternalProjection
