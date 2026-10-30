import LambdaCantor.AE.CenteredFactorSecond

noncomputable section

namespace LambdaCantor.AE

def centeredNormalizedFirst (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool × Bool) (ratio : ℝ) : ℝ :=
  exponent * (centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio)^(exponent-1) *
      centeredHorizontalFirst tailDepth (fun index => (digits index).1) ratio -
    exponent *
      (((verticalDepth : ℝ)-exponent*horizontalDepth)*ratio^((verticalDepth : ℝ)-exponent*horizontalDepth-1)*
          centeredTailFactor tailDepth (fun index => (digits index).2) ratio +
        ratio^((verticalDepth : ℝ)-exponent*horizontalDepth)*
          centeredDisplacementFirst 0 tailDepth (fun index => (digits index).2) ratio) +
    centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2) ratio

def centeredNormalizedSecond (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool × Bool) (ratio : ℝ) : ℝ :=
  exponent*(exponent-1)*
      (centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio)^(exponent-2)*
        (centeredHorizontalFirst tailDepth (fun index => (digits index).1) ratio)^2 +
    exponent*(centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio)^(exponent-1)*
      centeredHorizontalSecond tailDepth (fun index => (digits index).1) ratio -
    exponent *
      (((verticalDepth : ℝ)-exponent*horizontalDepth)*((verticalDepth : ℝ)-exponent*horizontalDepth-1)*
          ratio^((verticalDepth : ℝ)-exponent*horizontalDepth-2)*
            centeredTailFactor tailDepth (fun index => (digits index).2) ratio +
        2*((verticalDepth : ℝ)-exponent*horizontalDepth)*
          ratio^((verticalDepth : ℝ)-exponent*horizontalDepth-1)*
            centeredDisplacementFirst 0 tailDepth (fun index => (digits index).2) ratio +
        ratio^((verticalDepth : ℝ)-exponent*horizontalDepth)*
          centeredDisplacementSecond 0 tailDepth (fun index => (digits index).2) ratio) +
    centeredRemainderSecond exponent horizontalDepth verticalDepth tailDepth (fun index => (digits index).2) ratio

theorem centeredNormalizedResidual_first_actual (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (horizontal_positive : 0 < centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio)
    (vertical_small : ratio^verticalDepth < 1) :
    HasDerivAt (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits)
      (centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth digits ratio) ratio := by
  have horizontal := (centeredHorizontalFactor_first_actual tailDepth (fun index => (digits index).1) positive less_one).rpow_const
    (p := exponent) (Or.inl horizontal_positive.ne')
  have coefficient := (hasDerivAt_id ratio).rpow_const
    (p := (verticalDepth : ℝ)-exponent*horizontalDepth) (Or.inl positive.ne')
  have tail := centeredTailFactor_first_actual tailDepth (fun index => (digits index).2) positive less_one
  have remainder := centeredRemainderFunction_hasDerivAt exponent horizontalDepth verticalDepth tailDepth
    (fun index => (digits index).2) positive less_one vertical_small
  have model := (horizontal.sub ((coefficient.mul tail).const_mul exponent)).add remainder
  have hfunction := model.congr_of_eventuallyEq
    (f₁ := centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits)
    (Filter.Eventually.of_forall (fun parameter => by
      simp only [centeredNormalizedResidual, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
      <;> ring))
  apply hfunction.congr_deriv
  simp only [centeredNormalizedFirst, one_mul, id_eq]
  ring

/-- The genuine complete normalized residual has the displayed second
parameter derivative. In particular the baseline Newton C2 obligation is
about all three terms, not only its vertical nonlinear remainder. -/
theorem centeredNormalizedResidual_second_actual (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1)
    (horizontal_positive : 0 < centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio)
    (vertical_small : ratio^verticalDepth < 1) :
    HasDerivAt (centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth digits)
      (centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth digits ratio) ratio := by
  have horizontal := centeredHorizontalFactor_first_actual tailDepth (fun index => (digits index).1) positive less_one
  have horizontal_first := centeredHorizontalFactor_second_actual tailDepth (fun index => (digits index).1) positive less_one
  have horizontal_power := (horizontal.rpow_const (p := exponent-1) (Or.inl horizontal_positive.ne')).const_mul exponent
  have coefficient := (hasDerivAt_id ratio).rpow_const
    (p := (verticalDepth : ℝ)-exponent*horizontalDepth) (Or.inl positive.ne')
  have coefficient_first := ((hasDerivAt_id ratio).rpow_const
    (p := (verticalDepth : ℝ)-exponent*horizontalDepth-1) (Or.inl positive.ne')).const_mul
      ((verticalDepth : ℝ)-exponent*horizontalDepth)
  have tail := centeredTailFactor_first_actual tailDepth (fun index => (digits index).2) positive less_one
  have tail_first := centeredDisplacement_second_actual 0 tailDepth (fun index => (digits index).2) positive less_one
  have remainder := centeredRemainderFirst_hasDerivAt exponent horizontalDepth verticalDepth tailDepth
    (fun index => (digits index).2) positive less_one vertical_small
  have model := ((horizontal_power.mul horizontal_first).sub
    (((coefficient_first.mul tail).add (coefficient.mul tail_first)).const_mul exponent)).add remainder
  have exponent_shift : exponent-1-1 = exponent-2 := by ring
  have coefficient_shift : ((verticalDepth : ℝ)-exponent*horizontalDepth-1)-1 =
      (verticalDepth : ℝ)-exponent*horizontalDepth-2 := by ring
  have hfunction := model.congr_of_eventuallyEq
    (f₁ := centeredNormalizedFirst exponent horizontalDepth verticalDepth tailDepth digits)
    (Filter.Eventually.of_forall (fun parameter => by
      simp only [centeredNormalizedFirst, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
      <;> ring))
  apply hfunction.congr_deriv
  simp only [centeredNormalizedSecond, one_mul, id_eq, exponent_shift, coefficient_shift]
  ring

end LambdaCantor.AE
