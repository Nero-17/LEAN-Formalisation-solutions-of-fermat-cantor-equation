import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

/-- First-moment selection can avoid every null exceptional set. In
particular a real `toReal` energy minimizer can be chosen where the original
extended-real Fourier energy is finite. -/
theorem exists_freezing_point_le_average_with_ae_property
    (energy : ℝ → ℝ) (property : ℝ → Prop) {left right : ℝ}
    (ordered : left < right) (integrable : IntegrableOn energy (Icc left right))
    (property_ae : ∀ᵐ point ∂volume.restrict (Icc left right), property point) :
    ∃ point ∈ Icc left right, property point ∧
      energy point ≤ (right-left)⁻¹*∫ parameter in Icc left right, energy parameter := by
  classical
  have mass_nonzero : volume (Icc left right) ≠ 0 := by
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr ordered)).ne'
  have mass_finite : volume (Icc left right) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (volume.restrict (Icc left right)) := isFiniteMeasure_restrict.mpr mass_finite
  have restricted_nonzero : volume.restrict (Icc left right) ≠ 0 :=
    fun zero => mass_nonzero (Measure.restrict_eq_zero.mp zero)
  have good_ae : ∀ᵐ point ∂volume.restrict (Icc left right), point ∈ Icc left right ∧ property point :=
    (ae_restrict_mem measurableSet_Icc).and property_ae
  have bad_null : (volume.restrict (Icc left right)) {point | ¬(point ∈ Icc left right ∧ property point)} = 0 :=
    ae_iff.mp good_ae
  obtain ⟨point, avoids_bad, bound⟩ := exists_notMem_null_le_average restricted_nonzero integrable bad_null
  have good : point ∈ Icc left right ∧ property point := by
    simpa only [Set.mem_setOf_eq, not_not] using avoids_bad
  refine ⟨point, good.1, good.2, ?_⟩
  change energy point ≤ ⨍ parameter in Icc left right, energy parameter at bound
  simpa only [setAverage_eq, smul_eq_mul, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ordered.le)] using bound

theorem exists_finite_energy_freezing_point
    (energy : ℝ → ℝ≥0∞) {left right : ℝ}
    (ordered : left < right)
    (integrable : IntegrableOn (fun point => 1+(energy point).toReal) (Icc left right))
    (finite_ae : ∀ᵐ point ∂volume.restrict (Icc left right), energy point < ⊤) :
    ∃ point ∈ Icc left right, energy point < ⊤ ∧
      1+(energy point).toReal ≤
        (right-left)⁻¹*∫ parameter in Icc left right, 1+(energy parameter).toReal :=
  exists_freezing_point_le_average_with_ae_property
    (fun point => 1+(energy point).toReal) (fun point => energy point < ⊤)
    ordered integrable finite_ae

end LambdaCantor.AE
