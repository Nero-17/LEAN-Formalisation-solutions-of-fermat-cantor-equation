import LambdaCantor.AE.AddressPairInverseDensity
import LambdaCantor.AE.CancellationEstimate
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace LambdaCantor.AE

theorem hasCompactSupport_addressPairInverseDensity
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff : ℝ → ℝ) (hcompact : HasCompactSupport valueCutoff) :
    HasCompactSupport (addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hcompact ⊢
  exact hcompact.mono fun value hzero =>
    addressPairInverseDensity_zero_outside first second third fourth lower upper band
      parameterCutoff valueCutoff hzero

/-- The density has derivative zero off the cutoff's topological support,
even though the canonical inverse need not be regular away from its image. -/
theorem hasDerivAt_addressPairInverseDensity_outside_support
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff : ℝ → ℝ) {value : ℝ}
    (houtside : value ∉ tsupport valueCutoff) :
    HasDerivAt (addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) 0 value := by
  apply (hasDerivAt_const value (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [(isClosed_tsupport valueCutoff).isOpen_compl.mem_nhds houtside] with nearby hnearby
  exact addressPairInverseDensity_zero_outside first second third fourth lower upper band
    parameterCutoff valueCutoff (image_eq_zero_of_notMem_tsupport hnearby)

/-- Local derivative estimates on the cutoff support give a global
Lipschitz bound for the actual inverse density. The preceding derivative
formula supplies the local hypotheses when that support lies in the
interior of the actual residual image. -/
theorem lipschitzWith_addressPairInverseDensity
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff : ℝ → ℝ) (constant : ℝ≥0)
    (hlocal : ∀ value ∈ tsupport valueCutoff,
      DifferentiableAt ℝ (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value ∧
      |deriv (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value| ≤ constant) :
    LipschitzWith constant (addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) := by
  have hglobal : ∀ value,
      DifferentiableAt ℝ (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value ∧
      |deriv (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value| ≤ constant := by
    intro value
    by_cases hvalue : value ∈ tsupport valueCutoff
    · exact hlocal value hvalue
    · have hzero := hasDerivAt_addressPairInverseDensity_outside_support first second third fourth
        lower upper band parameterCutoff valueCutoff hvalue
      refine ⟨hzero.differentiableAt, ?_⟩
      rw [hzero.deriv, abs_zero]
      exact constant.coe_nonneg
  apply lipschitzWith_of_nnnorm_deriv_le (fun value => (hglobal value).1)
  intro value
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, Real.norm_eq_abs] using (hglobal value).2

/-- The near-band inverse-density integral has the required inverse-frequency
gain. This is the concrete transformed integral; identifying it with the
original parameter integral is a separate change-of-variables obligation. -/
theorem addressPairInverseDensity_cancellation_bound
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff kernel : ℝ → ℝ) (constant : ℝ≥0)
    {frequency : ℝ} (hfrequency : 0 < frequency)
    (hlocal : ∀ value ∈ tsupport valueCutoff,
      DifferentiableAt ℝ (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value ∧
      |deriv (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff) value| ≤ constant)
    (hkernel : Integrable kernel volume)
    (hproduct : Integrable (fun point => kernel point *
      addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff
        (point / frequency)) volume)
    (hmoment : Integrable (fun point => |point| * |kernel point|) volume)
    (hzero : ∫ point, kernel point = 0) :
    |∫ point, kernel point * addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff (point / frequency)| ≤
      ((constant : ℝ) / frequency) * ∫ point, |point| * |kernel point| := by
  exact integral_zero_mean_kernel_scaled_bound kernel
    (addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff)
    hfrequency
    (lipschitzWith_addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff constant hlocal)
    hkernel hproduct hmoment hzero

end LambdaCantor.AE
