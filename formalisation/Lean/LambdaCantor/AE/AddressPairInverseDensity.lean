import LambdaCantor.AE.AddressPairInverse
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
open Set

namespace LambdaCantor.AE

/-- The near-band inverse density for the actual address residual. The minus
sign is the absolute Jacobian because the residual is decreasing in this
orientation. A value cutoff supported in the interior image makes this
definition vanish outside that image without choosing an inverse there. -/
def addressPairInverseDensity (first second third fourth : ℕ → Bool)
    (lower upper band : ℝ) (parameterCutoff valueCutoff : ℝ → ℝ) (value : ℝ) : ℝ :=
  parameterCutoff (addressPairInverse first second third fourth lower upper band value) *
    valueCutoff value /
      (-deriv (addressPairDifference first second third fourth)
        (addressPairInverse first second third fourth lower upper band value))

theorem addressPairInverseDensity_zero_outside
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff : ℝ → ℝ) {value : ℝ}
    (hcutoff : valueCutoff value = 0) :
    addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff value = 0 := by
  simp only [addressPairInverseDensity, hcutoff, mul_zero, zero_div]

theorem addressPairInverseDensity_eq_absolute_jacobian
    (first second third fourth : ℕ → Bool) (lower upper band : ℝ)
    (parameterCutoff valueCutoff : ℝ → ℝ) {value : ℝ}
    (hnegative : deriv (addressPairDifference first second third fourth)
      (addressPairInverse first second third fourth lower upper band value) < 0) :
    addressPairInverseDensity first second third fourth lower upper band parameterCutoff valueCutoff value =
      parameterCutoff (addressPairInverse first second third fourth lower upper band value) *
        valueCutoff value /
        |deriv (addressPairDifference first second third fourth)
          (addressPairInverse first second third fourth lower upper band value)| := by
  rw [abs_of_neg hnegative]
  rfl

/-- The exact derivative after change of variables. In the three terms the
inverse Jacobian occurs respectively to powers two, one, and three. The
last term is the source of the factor b^depth/a^(3*depth). -/
theorem hasDerivAt_addressPairInverseDensity
    (first second third fourth : ℕ → Bool) {lower upper band margin value : ℝ}
    (parameterCutoff valueCutoff : ℝ → ℝ)
    (hband : 0 < band) (hmargin : 0 < margin)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hderivative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio ≤ -margin)
    (hvalue : value ∈ interior (addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band))
    (hparameter : DifferentiableAt ℝ parameterCutoff
      (addressPairInverse first second third fourth lower upper band value))
    (hcutoff : DifferentiableAt ℝ valueCutoff value)
    (hsecond : DifferentiableAt ℝ (deriv (addressPairDifference first second third fourth))
      (addressPairInverse first second third fourth lower upper band value)) :
    HasDerivAt (addressPairInverseDensity first second third fourth lower upper band
        parameterCutoff valueCutoff)
      (-(deriv parameterCutoff (addressPairInverse first second third fourth lower upper band value) *
          valueCutoff value) /
          (deriv (addressPairDifference first second third fourth)
            (addressPairInverse first second third fourth lower upper band value)) ^ 2 -
        (parameterCutoff (addressPairInverse first second third fourth lower upper band value) *
          deriv valueCutoff value) /
          deriv (addressPairDifference first second third fourth)
            (addressPairInverse first second third fourth lower upper band value) +
        (parameterCutoff (addressPairInverse first second third fourth lower upper band value) *
          valueCutoff value * deriv (deriv (addressPairDifference first second third fourth))
            (addressPairInverse first second third fourth lower upper band value)) /
          (deriv (addressPairDifference first second third fourth)
            (addressPairInverse first second third fourth lower upper band value)) ^ 3) value := by
  have hinverse := hasDerivAt_addressPairInverse first second third fourth
    hband hmargin hdifferentiable hderivative hvalue
  have hmembership := addressPairInverse_mem_and_right_inverse first second third fourth
    lower upper band (interior_subset hvalue)
  have hne : deriv (addressPairDifference first second third fourth)
      (addressPairInverse first second third fourth lower upper band value) ≠ 0 :=
    ne_of_lt ((hderivative _ hmembership.1.1 (abs_lt.mpr hmembership.1.2)).trans_lt
      (neg_neg_of_pos hmargin))
  have hnumerator := (hparameter.hasDerivAt.comp value hinverse).mul hcutoff.hasDerivAt
  have hdenominator := (hsecond.hasDerivAt.comp value hinverse).neg
  have hdensity := (hnumerator.div hdenominator (neg_ne_zero.mpr hne)).congr_of_eventuallyEq
    (f₁ := addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff)
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hdensity.congr_deriv
  simp only [Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
  field_simp [hne]
  <;> ring

/-- A quantitative derivative bound for the actual inverse density. This
algebraic bound is applied at the inverse parameter, with the three cutoff
and residual derivative estimates kept explicit. -/
theorem inverseDensity_derivative_expression_bound
    {parameterValue parameterDerivative cutoffValue cutoffDerivative residualDerivative
      residualSecondDerivative margin parameterBound parameterDerivativeBound cutoffBound
      cutoffDerivativeBound residualSecondBound : ℝ}
    (hmargin : 0 < margin) (hresidual : margin ≤ |residualDerivative|)
    (hparameter : |parameterValue| ≤ parameterBound)
    (hparameterDerivative : |parameterDerivative| ≤ parameterDerivativeBound)
    (hcutoff : |cutoffValue| ≤ cutoffBound)
    (hcutoffDerivative : |cutoffDerivative| ≤ cutoffDerivativeBound)
    (hsecond : |residualSecondDerivative| ≤ residualSecondBound) :
    |-(parameterDerivative * cutoffValue) / residualDerivative ^ 2 -
      (parameterValue * cutoffDerivative) / residualDerivative +
      (parameterValue * cutoffValue * residualSecondDerivative) / residualDerivative ^ 3| ≤
      parameterDerivativeBound * cutoffBound / margin ^ 2 +
        parameterBound * cutoffDerivativeBound / margin +
        parameterBound * cutoffBound * residualSecondBound / margin ^ 3 := by
  have hparameterNonneg := (abs_nonneg parameterValue).trans hparameter
  have hparameterDerivativeNonneg := (abs_nonneg parameterDerivative).trans hparameterDerivative
  have hcutoffNonneg := (abs_nonneg cutoffValue).trans hcutoff
  have hcutoffDerivativeNonneg := (abs_nonneg cutoffDerivative).trans hcutoffDerivative
  have hsecondNonneg := (abs_nonneg residualSecondDerivative).trans hsecond
  have hfirstNumerator : |parameterDerivative| * |cutoffValue| ≤
      parameterDerivativeBound * cutoffBound :=
    mul_le_mul hparameterDerivative hcutoff (abs_nonneg _) hparameterDerivativeNonneg
  have hsecondNumerator : |parameterValue| * |cutoffDerivative| ≤
      parameterBound * cutoffDerivativeBound :=
    mul_le_mul hparameter hcutoffDerivative (abs_nonneg _) hparameterNonneg
  have hthirdNumerator : |parameterValue| * |cutoffValue| * |residualSecondDerivative| ≤
      parameterBound * cutoffBound * residualSecondBound :=
    mul_le_mul (mul_le_mul hparameter hcutoff (abs_nonneg _) hparameterNonneg)
      hsecond (abs_nonneg _) (mul_nonneg hparameterNonneg hcutoffNonneg)
  have hfirst := div_le_div₀ (by positivity : 0 ≤ parameterDerivativeBound * cutoffBound)
    hfirstNumerator (by positivity : 0 < margin ^ 2)
    (pow_le_pow_left₀ hmargin.le hresidual 2)
  have hmiddle := div_le_div₀ (by positivity : 0 ≤ parameterBound * cutoffDerivativeBound)
    hsecondNumerator hmargin hresidual
  have hlast := div_le_div₀ (by positivity : 0 ≤ parameterBound * cutoffBound * residualSecondBound)
    hthirdNumerator (by positivity : 0 < margin ^ 3)
    (pow_le_pow_left₀ hmargin.le hresidual 3)
  calc
    _ ≤ |-(parameterDerivative * cutoffValue) / residualDerivative ^ 2 -
        (parameterValue * cutoffDerivative) / residualDerivative| +
        |(parameterValue * cutoffValue * residualSecondDerivative) / residualDerivative ^ 3| := abs_add_le _ _
    _ ≤ (|-(parameterDerivative * cutoffValue) / residualDerivative ^ 2| +
        |(parameterValue * cutoffDerivative) / residualDerivative|) +
        |(parameterValue * cutoffValue * residualSecondDerivative) / residualDerivative ^ 3| :=
      add_le_add (abs_sub _ _) (le_refl _)
    _ ≤ _ := by
      simp only [abs_div, abs_neg, abs_mul, abs_pow]
      exact add_le_add (add_le_add hfirst hmiddle) hlast

/-- The quantitative estimate applied to the actual inverse density. Its
last denominator is margin cubed; with margin=c*lower^depth and the second
derivative bound C*(depth+1)^2*upper^depth this gives the required exponential
factor (upper/lower^3)^depth. -/
theorem deriv_addressPairInverseDensity_bound
    (first second third fourth : ℕ → Bool) {lower upper band margin value : ℝ}
    (parameterCutoff valueCutoff : ℝ → ℝ)
    {parameterBound parameterDerivativeBound cutoffBound cutoffDerivativeBound residualSecondBound : ℝ}
    (hband : 0 < band) (hmargin : 0 < margin)
    (hdifferentiable : ∀ ratio ∈ Ioo lower upper,
      DifferentiableAt ℝ (addressPairDifference first second third fourth) ratio)
    (hderivative : ∀ ratio ∈ Ioo lower upper,
      |addressPairDifference first second third fourth ratio| < band →
        deriv (addressPairDifference first second third fourth) ratio ≤ -margin)
    (hvalue : value ∈ interior (addressPairDifference first second third fourth ''
      addressPairBand first second third fourth lower upper band))
    (hparameter : DifferentiableAt ℝ parameterCutoff
      (addressPairInverse first second third fourth lower upper band value))
    (hcutoff : DifferentiableAt ℝ valueCutoff value)
    (hsecond : DifferentiableAt ℝ (deriv (addressPairDifference first second third fourth))
      (addressPairInverse first second third fourth lower upper band value))
    (hparameterBound : |parameterCutoff
      (addressPairInverse first second third fourth lower upper band value)| ≤ parameterBound)
    (hparameterDerivativeBound : |deriv parameterCutoff
      (addressPairInverse first second third fourth lower upper band value)| ≤ parameterDerivativeBound)
    (hcutoffBound : |valueCutoff value| ≤ cutoffBound)
    (hcutoffDerivativeBound : |deriv valueCutoff value| ≤ cutoffDerivativeBound)
    (hsecondBound : |deriv (deriv (addressPairDifference first second third fourth))
      (addressPairInverse first second third fourth lower upper band value)| ≤ residualSecondBound) :
    |deriv (addressPairInverseDensity first second third fourth lower upper band
      parameterCutoff valueCutoff) value| ≤
      parameterDerivativeBound * cutoffBound / margin ^ 2 +
        parameterBound * cutoffDerivativeBound / margin +
        parameterBound * cutoffBound * residualSecondBound / margin ^ 3 := by
  rw [(hasDerivAt_addressPairInverseDensity first second third fourth parameterCutoff valueCutoff
    hband hmargin hdifferentiable hderivative hvalue hparameter hcutoff hsecond).deriv]
  apply inverseDensity_derivative_expression_bound hmargin ?_ hparameterBound
    hparameterDerivativeBound hcutoffBound hcutoffDerivativeBound hsecondBound
  have hmembership := addressPairInverse_mem_and_right_inverse first second third fourth
    lower upper band (interior_subset hvalue)
  have hbound := hderivative _ hmembership.1.1 (abs_lt.mpr hmembership.1.2)
  have habsolute := neg_le_abs (deriv (addressPairDifference first second third fourth)
    (addressPairInverse first second third fourth lower upper band value))
  linarith

end LambdaCantor.AE
