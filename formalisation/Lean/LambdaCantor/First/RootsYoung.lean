import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory

namespace LambdaCantor.First.Roots

theorem translated_function_integrable (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (function : ℝ → ℝ) (measurable : Measurable function) (integrable : Integrable function volume) :
    Integrable (fun point : ℝ × ℝ => function (point.1 - point.2)) (volume.prod measure) := by
  apply (integrable_prod_iff' (measurable.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun shift => integrable.comp_sub_right shift)
  · have constant_identity : (fun shift : ℝ => ∫ point : ℝ, ‖function (point - shift)‖) =
        (fun _ => ∫ point : ℝ, ‖function point‖) := by
      funext shift
      exact integral_sub_right_eq_self (fun point => ‖function point‖) shift
    dsimp only [Function.comp_apply, Pi.sub_apply]
    rw [constant_identity]
    exact integrable_const _

theorem translated_average_integrable (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (function : ℝ → ℝ) (measurable : Measurable function) (integrable : Integrable function volume) :
    Integrable (fun point : ℝ => ∫ shift, function (point - shift) ∂measure) volume :=
  (translated_function_integrable measure function measurable integrable).integral_prod_left

theorem translated_average_integral (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (function : ℝ → ℝ) (measurable : Measurable function) (integrable : Integrable function volume) :
    (∫ point : ℝ, ∫ shift, function (point - shift) ∂measure) = ∫ point : ℝ, function point := by
  rw [integral_integral_swap (translated_function_integrable measure function measurable integrable)]
  simp only [integral_sub_right_eq_self, integral_const, probReal_univ,
    one_smul]

/-- The elementary probability-space L2 averaging contraction. -/
theorem square_integral_le_integral_square (measure : Measure ℝ)
    [IsProbabilityMeasure measure] (function : ℝ → ℝ)
    (square_integrable : MemLp function 2 measure) :
    (∫ point, function point ∂measure) ^ 2 ≤ ∫ point, function point ^ 2 ∂measure := by
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := measure) Real.HolderConjugate.two_two
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun point => ‖function point‖)
    (Filter.Eventually.of_forall (fun _ => zero_le_one))
    (Filter.Eventually.of_forall (fun point => norm_nonneg (function point)))
    (by simpa using (memLp_const (μ := measure) (p := 2) (1 : ℝ)))
    (by simpa using square_integrable.norm)
  have norm_bound : ‖∫ point, function point ∂measure‖ ≤
      Real.sqrt (∫ point, function point ^ 2 ∂measure) := by
    calc
      _ ≤ ∫ point, ‖function point‖ ∂measure := norm_integral_le_integral_norm _
      _ ≤ _ := by
        simpa [Real.rpow_two, Real.sqrt_eq_rpow, one_div, Real.norm_eq_abs, sq_abs] using holder
  have squared := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 norm_bound
  simpa [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] using squared

/-- Joint square integrability implies square integrability after averaging
over a probability measure. This is the required special case of Minkowski,
proved internally from Cauchy--Schwarz and Fubini. -/
theorem averaging_memLp_two (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (function : ℝ × ℝ → ℝ) (measurable : Measurable function)
    (square_integrable : Integrable (fun point => function point ^ 2) (volume.prod measure)) :
    MemLp (fun point : ℝ => ∫ shift, function (point, shift) ∂measure) 2 volume := by
  have average_measurable := measurable.stronglyMeasurable.integral_prod_right' (ν := measure)
  apply (memLp_two_iff_integrable_sq average_measurable.aestronglyMeasurable).2
  apply square_integrable.integral_prod_left.mono'
  · exact (average_measurable.pow 2).aestronglyMeasurable
  · filter_upwards [square_integrable.prod_right_ae] with point section_integrable
    have section_measurable : Measurable (fun shift => function (point, shift)) :=
      measurable.comp (measurable_const.prodMk measurable_id)
    have section_memLp := (memLp_two_iff_integrable_sq
      section_measurable.stronglyMeasurable.aestronglyMeasurable).2 section_integrable
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (∫ shift, function (point, shift) ∂measure))] using!
      square_integral_le_integral_square measure (fun shift => function (point, shift)) section_memLp

/-- Averaging all translates against any probability measure preserves L2,
even when that averaging measure is singular. -/
theorem translated_average_memLp_two (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (function : ℝ → ℝ) (measurable : Measurable function)
    (square_integrable : MemLp function 2 volume) :
    MemLp (fun point : ℝ => ∫ shift, function (point - shift) ∂measure) 2 volume := by
  apply averaging_memLp_two measure (fun point => function (point.1 - point.2))
    (measurable.comp (by fun_prop))
  have square_integrable' : Integrable (fun point => function point ^ 2) volume :=
    (memLp_two_iff_integrable_sq measurable.stronglyMeasurable.aestronglyMeasurable).1 square_integrable
  apply (integrable_prod_iff' ((measurable.comp (measurable_fst.sub measurable_snd)).pow_const 2).stronglyMeasurable.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun shift => square_integrable'.comp_sub_right shift)
  · have constant_identity : (fun shift : ℝ => ∫ point : ℝ, ‖function (point - shift) ^ 2‖) =
        (fun _ => ∫ point : ℝ, ‖function point ^ 2‖) := by
      funext shift
      exact integral_sub_right_eq_self (fun point => ‖function point ^ 2‖) shift
    dsimp only [Function.comp_apply, Pi.sub_apply]
    rw [constant_identity]
    exact integrable_const _

end LambdaCantor.First.Roots


