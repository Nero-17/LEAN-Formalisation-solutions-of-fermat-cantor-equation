import LambdaCantor.First.RootsKernelTails
import LambdaCantor.First.ProjectionMeasure

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

def prependPairedDigit (digit : Bool × Bool) (tail : ℕ → Bool × Bool) : ℕ → Bool × Bool :=
  fun index => if index = 0 then digit else tail (index - 1)

theorem continuous_prependPairedDigit :
    Continuous (fun point : (Bool × Bool) × (ℕ → Bool × Bool) => prependPairedDigit point.1 point.2) := by
  apply continuous_pi
  intro index
  by_cases zero : index = 0
  · simpa only [prependPairedDigit, if_pos zero] using
      (continuous_fst : Continuous (fun point : (Bool × Bool) × (ℕ → Bool × Bool) => point.1))
  · have coordinate_continuous : Continuous (fun tail : ℕ → Bool × Bool => tail (index - 1)) :=
      continuous_apply (index - 1)
    have tail_continuous : Continuous (fun point : (Bool × Bool) × (ℕ → Bool × Bool) => point.2) :=
      continuous_snd
    simpa only [prependPairedDigit, if_neg zero, Function.comp_def] using
      coordinate_continuous.comp tail_continuous

/-- Exact first-digit disintegration for any measurable full-tail observable.
The factors are the actual fair paired product measure, with no conditional
restriction of the fresh tails. -/
theorem pairedLaw_firstdigit_split (function : (ℕ → Bool × Bool) → ℝ)
    (measurable : Measurable function) :
    pairedAddressMeasure.map function = ∑ digit : Bool × Bool,
      (4 : ℝ≥0∞)⁻¹ • pairedAddressMeasure.map (fun tail => function (prependPairedDigit digit tail)) := by
  let combine : (Bool × Bool) × (ℕ → Bool × Bool) → ℝ :=
    fun point => function (prependPairedDigit point.1 point.2)
  have combine_measurable : Measurable combine := measurable.comp continuous_prependPairedDigit.measurable
  have mapped : pairedAddressMeasure.map function =
      ((PMF.uniformOfFintype (Bool × Bool)).toMeasure.prod pairedAddressMeasure).map combine := by
    rw [← LambdaCantor.First.PrefixSlopes.paired_head_tail_law,
      Measure.map_map combine_measurable (by fun_prop)]
    congr 1
    funext digits
    congr 1
    funext index
    dsimp [combine, prependPairedDigit]
    split_ifs with zero
    · subst index
      rfl
    · congr 1
      omega
  rw [mapped, LambdaCantor.First.PrefixSlopes.uniform_paired_measure_eq_sum,
    Measure.prod_sum_left, Measure.map_sum combine_measurable.aemeasurable]
  simp_rw [Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map combine_measurable measurable_prodMk_left]
  rw [Measure.sum_fintype]
  rfl

def completeRootKernelLaw {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) : Measure ℝ :=
  pairedAddressMeasure.map (completeRootKernel data representative depth)

theorem completeRootKernelLaw_probability {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    IsProbabilityMeasure (completeRootKernelLaw data representative depth) := by
  unfold completeRootKernelLaw
  exact Measure.isProbabilityMeasure_map (continuous_completeRootKernel data representative depth).measurable.aemeasurable

theorem completeRootKernelLaw_firstdigit_split {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ) :
    completeRootKernelLaw data representative depth = ∑ digit : Bool × Bool,
      (4 : ℝ≥0∞)⁻¹ • pairedAddressMeasure.map
        (fun tail => completeRootKernel data representative depth (prependPairedDigit digit tail)) :=
  pairedLaw_firstdigit_split _ (continuous_completeRootKernel data representative depth).measurable

end LambdaCantor.First.Roots
