import LambdaCantor.AE.NewtonMixture
import LambdaCantor.AE.CommonSourceCoupling

noncomputable section
open MeasureTheory

namespace LambdaCantor.AE

def FrozenNewtonKernel.affineCenter (kernel : FrozenNewtonKernel) : ℝ :=
  kernel.freezing-kernel.residual/kernel.parameterDerivative

def FrozenNewtonKernel.firstScale (kernel : FrozenNewtonKernel) : ℝ :=
  -kernel.firstCoefficient/kernel.parameterDerivative

def FrozenNewtonKernel.secondScale (kernel : FrozenNewtonKernel) : ℝ :=
  -kernel.secondCoefficient/kernel.parameterDerivative

theorem FrozenNewtonKernel.value_eq_affine (kernel : FrozenNewtonKernel) (digits : ℕ → Bool × Bool) :
    kernel.value digits = kernel.affineCenter +
      kernel.firstScale*address kernel.freezing (fun index => (digits index).1) +
      kernel.secondScale*address kernel.freezing (fun index => (digits index).2) := by
  unfold FrozenNewtonKernel.value centeredNewtonValue FrozenNewtonKernel.affineCenter
    FrozenNewtonKernel.firstScale FrozenNewtonKernel.secondScale
  ring

/-- Normalization changes the output coordinate while retaining the actual
Cantor contraction parameter. It is therefore expressed directly as a law. -/
def normalizedNewtonLaw (kernel : FrozenNewtonKernel) (origin width : ℝ) : Measure ℝ :=
  kernel.law.map (fun value => (value-origin)/width)

theorem normalizedNewtonLaw_eq_affine (kernel : FrozenNewtonKernel) (origin width : ℝ) :
    normalizedNewtonLaw kernel origin width =
      affineConvolutionProbability kernel.freezing ((kernel.affineCenter-origin)/width)
        (kernel.firstScale/width) (kernel.secondScale/width) := by
  have normalization_measurable : Measurable (fun value : ℝ => (value - origin) / width) := by fun_prop
  rw [normalizedNewtonLaw, kernel.law_eq_paired_map,
    Measure.map_map normalization_measurable kernel.value_measurable,
    affineConvolutionProbability_eq_address_map]
  rw [← paired_address_streams_product_law,
    Measure.map_map (by
      have first : Measurable (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
          address kernel.freezing digits.1) :=
        (measurable_address_digits kernel.freezing).comp measurable_fst
      have second : Measurable (fun digits : (ℕ → Bool) × (ℕ → Bool) =>
          address kernel.freezing digits.2) :=
        (measurable_address_digits kernel.freezing).comp measurable_snd
      exact measurable_const.add ((first.const_mul _).add (second.const_mul _))) (by fun_prop)]
  congr 1
  funext digits
  simp only [Function.comp_apply, FrozenNewtonKernel.value_eq_affine]
  ring

theorem FrozenNewtonKernel.value_affine_support (kernel : FrozenNewtonKernel)
    (ratio_nonnegative : 0 ≤ kernel.freezing) (ratio_less_one : kernel.freezing < 1)
    (first_nonnegative : 0 ≤ kernel.firstScale) (second_nonnegative : 0 ≤ kernel.secondScale)
    (digits : ℕ → Bool × Bool) :
    |kernel.value digits-kernel.affineCenter| ≤ kernel.firstScale+kernel.secondScale := by
  rw [kernel.value_eq_affine]
  have first_lower := mul_nonneg first_nonnegative
    (address_nonnegative ratio_nonnegative ratio_less_one (fun index => (digits index).1))
  have second_lower := mul_nonneg second_nonnegative
    (address_nonnegative ratio_nonnegative ratio_less_one (fun index => (digits index).2))
  have first_upper := mul_le_mul_of_nonneg_left
    (address_le_one ratio_nonnegative ratio_less_one (fun index => (digits index).1)) first_nonnegative
  have second_upper := mul_le_mul_of_nonneg_left
    (address_le_one ratio_nonnegative ratio_less_one (fun index => (digits index).2)) second_nonnegative
  apply abs_le.mpr
  constructor <;> linarith

end LambdaCantor.AE
