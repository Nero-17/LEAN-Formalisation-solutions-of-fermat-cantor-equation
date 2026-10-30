import LambdaCantor.First.RootsKernelDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

/-- A density of a concentrated law has a representative vanishing everywhere
outside its support; this preserves the actual law and L1/L2 properties. -/
theorem supportedL2Density_exists {measure : Measure ℝ}
    (density_exists : LinearRegularity.HasL2Density measure)
    (support : Set ℝ) (support_measurable : MeasurableSet support)
    (concentrated : measure supportᶜ = 0) :
    ∃ density : ℝ → ℝ, (∀ point, 0 ≤ density point) ∧ Measurable density ∧
      Integrable density volume ∧ MemLp density 2 volume ∧
      measure = volume.withDensity (fun point => ENNReal.ofReal (density point)) ∧
      ∀ point, point ∉ support → density point = 0 := by
  obtain ⟨density, nonnegative, measurable, integrable, square, law⟩ := density_exists
  have supported : ∀ᵐ point ∂measure, point ∈ support := by
    rw [ae_iff]
    exact concentrated
  rw [law] at supported
  have density_support := (ae_withDensity_iff measurable.ennreal_ofReal).mp supported
  have agrees : support.indicator density =ᵐ[volume] density := by
    filter_upwards [density_support] with point point_property
    by_cases member : point ∈ support
    · exact Set.indicator_of_mem member density
    · have zero_real : ENNReal.ofReal (density point) = 0 := by
        by_contra nonzero
        exact member (point_property nonzero)
      have zero : density point = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp zero_real) (nonnegative point)
      simp only [Set.indicator_of_notMem member, zero]
  refine ⟨support.indicator density, ?_, measurable.indicator support_measurable,
    integrable.indicator support_measurable, square.indicator support_measurable, ?_, ?_⟩
  · intro point
    by_cases member : point ∈ support
    · simpa only [Set.indicator_of_mem member] using nonnegative point
    · simp only [Set.indicator_of_notMem member, le_refl]
  · rw [law]
    apply withDensity_congr_ae
    filter_upwards [agrees] with point equality
    exact congrArg ENNReal.ofReal equality.symm
  · intro point outside
    exact Set.indicator_of_notMem outside density

end LambdaCantor.First.Roots
