import LambdaCantor.First.LinearRegularityExternal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

def affineDensity (center scale : ℝ) (density : ℝ → ℝ) (point : ℝ) : ℝ :=
  |scale|⁻¹ * density ((point - center) / scale)

theorem affineDensity_integrable (center scale : ℝ) (scale_nonzero : scale ≠ 0)
    (density : ℝ → ℝ) (integrable : Integrable density volume) :
    Integrable (affineDensity center scale density) volume := by
  have transformed := ((integrable.comp_mul_right' (inv_ne_zero scale_nonzero)).comp_sub_right center).const_mul |scale|⁻¹
  change Integrable (fun point => |scale|⁻¹ * density ((point - center) / scale)) volume
  simpa only [div_eq_mul_inv] using! transformed

theorem affineDensity_memLp_two (center scale : ℝ) (scale_nonzero : scale ≠ 0)
    (density : ℝ → ℝ) (measurable : Measurable density) (square_integrable : MemLp density 2 volume) :
    MemLp (affineDensity center scale density) 2 volume := by
  have density_square := (memLp_two_iff_integrable_sq measurable.aestronglyMeasurable).1 square_integrable
  have transformed := ((density_square.comp_mul_right' (inv_ne_zero scale_nonzero)).comp_sub_right center).const_mul (|scale|⁻¹ ^ 2)
  apply (memLp_two_iff_integrable_sq (show Measurable (affineDensity center scale density) by
    unfold affineDensity; fun_prop).aestronglyMeasurable).2
  simpa only [affineDensity, div_eq_mul_inv, mul_pow] using transformed

theorem affine_map_volume (center scale : ℝ) (scale_nonzero : scale ≠ 0) :
    volume.map (fun point : ℝ => center + scale * point) = ENNReal.ofReal |scale|⁻¹ • volume := by
  have composition : volume.map (fun point : ℝ => center + scale * point) =
      (volume.map (fun point : ℝ => scale * point)).map (fun point : ℝ => center + point) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [composition, Real.map_volume_mul_left scale_nonzero, Measure.map_smul,
    map_add_left_eq_self]
  simp only [abs_inv]

/-- Exact density change of variables for a nondegenerate real affine map. -/
theorem affine_map_withDensity (center scale : ℝ) (scale_nonzero : scale ≠ 0)
    (density : ℝ → ℝ) (measurable : Measurable density) :
    (volume.withDensity (fun point => ENNReal.ofReal (density point))).map
      (fun point : ℝ => center + scale * point) =
      volume.withDensity (fun point => ENNReal.ofReal (affineDensity center scale density point)) := by
  have transported : (volume.withDensity (fun point => ENNReal.ofReal (density point))).map
      (fun point : ℝ => center + scale * point) =
      (volume.map (fun point : ℝ => center + scale * point)).withDensity
        (fun point => ENNReal.ofReal (density ((point - center) / scale))) := by
    apply Measure.ext
    intro set set_measurable
    have affine_measurable : Measurable (fun point : ℝ => center + scale * point) := by fun_prop
    have preimage_measurable : MeasurableSet ((fun point : ℝ => center + scale * point) ⁻¹' set) :=
      affine_measurable set_measurable
    rw [Measure.map_apply affine_measurable set_measurable,
      withDensity_apply _ preimage_measurable, withDensity_apply _ set_measurable,
      setLIntegral_map set_measurable (by fun_prop) (by fun_prop)]
    apply lintegral_congr
    intro point
    congr 2
    field_simp [scale_nonzero]
    <;> ring
  rw [transported, affine_map_volume center scale scale_nonzero, withDensity_smul_measure,
    ← withDensity_smul _ (by fun_prop)]
  congr 1
  funext point
  simp only [Pi.smul_apply, smul_eq_mul, affineDensity,
    ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg scale))]

theorem hasL2Density_affine {measure : Measure ℝ} (density_exists : LinearRegularity.HasL2Density measure)
    (center scale : ℝ) (scale_nonzero : scale ≠ 0) :
    LinearRegularity.HasL2Density (measure.map (fun point : ℝ => center + scale * point)) := by
  obtain ⟨density, nonnegative, measurable, integrable, square_integrable, law⟩ := density_exists
  refine ⟨affineDensity center scale density, ?_, ?_,
    affineDensity_integrable center scale scale_nonzero density integrable,
    affineDensity_memLp_two center scale scale_nonzero density measurable square_integrable, ?_⟩
  · intro point
    exact mul_nonneg (inv_nonneg.mpr (abs_nonneg scale)) (nonnegative _)
  · unfold affineDensity
    fun_prop
  · rw [law]
    exact affine_map_withDensity center scale scale_nonzero density measurable

end LambdaCantor.First.Roots
