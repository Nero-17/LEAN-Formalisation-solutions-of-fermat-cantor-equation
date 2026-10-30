import LambdaCantor.First.PrefixCylinder
import Mathlib.MeasureTheory.Integral.Average

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LambdaCantor.AE
open First.PrefixSlopes

/-- Root-image containment converts weighted interval overlap to root-law mass.
Both the law and the prefix masses here are the actual paired-address ones. -/
theorem root_prefix_interval_overlap
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    (depth : ℕ) (centres : (Fin depth → Bool × Bool) → ℝ)
    {radius point : ℝ}
    (displacement : ∀ word digits, digits ∈ prefixCylinder word →
      root digits ∈ Icc (centres word-radius) (centres word+radius)) :
    ((Finset.univ.filter (fun word => point ∈ Icc (centres word-radius) (centres word+radius))).card : ℝ≥0∞)
        * (1/4 : ℝ≥0∞)^depth ≤
      First.Roots.rootLaw root (Icc (point-2*radius) (point+2*radius)) := by
  classical
  apply First.cylinder_count_from_mass First.Roots.pairedAddressMeasure
    (Finset.univ.filter (fun word => point ∈ Icc (centres word-radius) (centres word+radius)))
    prefixCylinder (root ⁻¹' Icc (point-2*radius) (point+2*radius)) ((1/4 : ℝ≥0∞)^depth)
  · intro left _ right _ different
    exact prefixCylinder_disjoint different
  · intro word _
    exact prefixCylinder_measurable word
  · intro word _
    exact (prefixCylinder_mass word).ge
  · intro word selected digits prefix_mem
    have point_bounds := (Finset.mem_filter.mp selected).2
    have root_bounds := displacement word digits prefix_mem
    constructor <;> linarith [point_bounds.1, point_bounds.2, root_bounds.1, root_bounds.2]
  · rw [First.Roots.rootLaw, Measure.map_apply root_measurable measurableSet_Icc]

/-- The small-ball input is kept explicit; the conclusion is the actual weighted
prefix overlap required for freezing. -/
theorem root_prefix_interval_overlap_of_smallBall
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    (depth : ℕ) (centres : (Fin depth → Bool × Bool) → ℝ)
    {radius point : ℝ} {bound : ℝ≥0∞}
    (displacement : ∀ word digits, digits ∈ prefixCylinder word →
      root digits ∈ Icc (centres word-radius) (centres word+radius))
    (small_ball : First.Roots.rootLaw root (Icc (point-2*radius) (point+2*radius)) ≤ bound) :
    ((Finset.univ.filter (fun word => point ∈ Icc (centres word-radius) (centres word+radius))).card : ℝ≥0∞)
        * (1/4 : ℝ≥0∞)^depth ≤ bound :=
  (root_prefix_interval_overlap root root_measurable depth centres displacement).trans small_ball

/-- A freezing point can be chosen with energy at most its interval average,
which is stronger than the manuscript's factor-two bound. -/
theorem exists_freezing_point_le_average (energy : ℝ → ℝ) {left right : ℝ}
    (ordered : left < right) (integrable : IntegrableOn energy (Icc left right)) :
    ∃ point ∈ Icc left right,
      energy point ≤ (right-left)⁻¹ * ∫ parameter in Icc left right, energy parameter := by
  have mass_nonzero : volume (Icc left right) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr ordered)).ne'
  have mass_finite : volume (Icc left right) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨point, point_mem, bound⟩ := exists_le_setAverage mass_nonzero mass_finite integrable
  refine ⟨point, point_mem, ?_⟩
  simpa [setAverage_eq, smul_eq_mul, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ordered.le)] using bound

end LambdaCantor.AE

