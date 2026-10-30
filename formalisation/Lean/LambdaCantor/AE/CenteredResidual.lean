import LambdaCantor.AE.CenteredC2Decay

noncomputable section
namespace LambdaCantor.AE

def centeredHorizontalFactor (tailDepth : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  1 - ratio ^ tailDepth + ratio ^ tailDepth * address ratio digits

def centeredTailFactor (tailDepth : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  1 - ratio ^ tailDepth * address ratio digits

def centeredNormalizedResidual (exponent : ℝ) (horizontalDepth verticalDepth tailDepth : ℕ)
    (digits : ℕ → Bool × Bool) (ratio : ℝ) : ℝ :=
  (centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio) ^ exponent -
    exponent * ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) *
      centeredTailFactor tailDepth (fun index => (digits index).2) ratio +
    centeredRemainderFunction exponent horizontalDepth verticalDepth tailDepth
      (fun index => (digits index).2) ratio

theorem centeredNormalizedResidual_actual (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio =
      (((centeredCylinder ratio horizontalDepth verticalDepth tailDepth
          (address ratio (fun index => (digits index).1), address ratio (fun index => (digits index).2))).1 ^ exponent +
        (centeredCylinder ratio horizontalDepth verticalDepth tailDepth
          (address ratio (fun index => (digits index).1), address ratio (fun index => (digits index).2))).2 ^ exponent - 1) /
        ratio ^ (exponent * horizontalDepth)) := by
  rw [centeredCylinder_residual exponent ratio hpositive hless horizontalDepth verticalDepth tailDepth
    _ (address_nonnegative hpositive.le hless _)]
  simp only [centeredNormalizedResidual, centeredHorizontalFactor, centeredTailFactor,
    centeredRemainderFunction, centeredAddressDisplacement, Prod.fst, Prod.snd]
  rw [show -exponent * (horizontalDepth : ℝ) = -(exponent * horizontalDepth) by ring,
    Real.rpow_neg hpositive.le]
  ring

theorem centeredHorizontalFactor_hasDerivAt (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    HasDerivAt (centeredHorizontalFactor tailDepth digits)
      (-(tailDepth : ℝ) * ratio ^ (tailDepth - 1) +
        (tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio digits +
        ratio ^ tailDepth * deriv (fun parameter => address parameter digits) ratio) ratio := by
  have haddress := (hasDerivAt_address_parameter hpositive hless digits).differentiableAt.hasDerivAt
  have hmodel := ((hasDerivAt_pow tailDepth ratio).const_sub 1).add
    ((hasDerivAt_pow tailDepth ratio).mul haddress)
  have hfunction := hmodel.congr_of_eventuallyEq
    (f₁ := centeredHorizontalFactor tailDepth digits)
    (Filter.Eventually.of_forall (fun _ => rfl))
  apply hfunction.congr_deriv
  ring

theorem centeredTailFactor_hasDerivAt (tailDepth : ℕ) (digits : ℕ → Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1) :
    HasDerivAt (centeredTailFactor tailDepth digits)
      (-((tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio digits +
        ratio ^ tailDepth * deriv (fun parameter => address parameter digits) ratio)) ratio := by
  have haddress := (hasDerivAt_address_parameter hpositive hless digits).differentiableAt.hasDerivAt
  exact ((hasDerivAt_pow tailDepth ratio).mul haddress).const_sub 1

theorem centeredNormalizedResidual_hasDerivAt (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (hhorizontal : 0 < centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio)
    (hvertical : ratio ^ verticalDepth < 1) :
    HasDerivAt (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits)
      (((-(tailDepth : ℝ) * ratio ^ (tailDepth - 1) +
          (tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio (fun index => (digits index).1) +
          ratio ^ tailDepth * deriv (fun parameter => address parameter (fun index => (digits index).1)) ratio) *
          exponent * (centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio) ^ (exponent - 1)) -
        exponent * (((verticalDepth : ℝ) - exponent * horizontalDepth) *
          ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth - 1) *
          centeredTailFactor tailDepth (fun index => (digits index).2) ratio -
          ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) *
            ((tailDepth : ℝ) * ratio ^ (tailDepth - 1) * address ratio (fun index => (digits index).2) +
              ratio ^ tailDepth * deriv (fun parameter => address parameter (fun index => (digits index).2)) ratio)) +
        centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth
          (fun index => (digits index).2) ratio) ratio := by
  have hpower := (centeredHorizontalFactor_hasDerivAt tailDepth
    (fun index => (digits index).1) hpositive hless).rpow_const (p := exponent)
      (Or.inl (ne_of_gt hhorizontal))
  have hcoefficient := (hasDerivAt_id ratio).rpow_const
    (p := (verticalDepth : ℝ) - exponent * horizontalDepth) (Or.inl (ne_of_gt hpositive))
  have htail := centeredTailFactor_hasDerivAt tailDepth (fun index => (digits index).2) hpositive hless
  have hremainder := centeredRemainderFunction_hasDerivAt exponent horizontalDepth verticalDepth tailDepth
    (fun index => (digits index).2) hpositive hless hvertical
  have hmodel := (hpower.sub ((hcoefficient.mul htail).const_mul exponent)).add hremainder
  have hfunction := hmodel.congr_of_eventuallyEq
    (f₁ := centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits)
    (Filter.Eventually.of_forall (fun parameter => by
      simp only [centeredNormalizedResidual, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
      ring))
  apply hfunction.congr_deriv
  simp only [one_mul, id_eq]
  ring

theorem centeredNormalizedResidual_deriv (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (hhorizontal : 0 < centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio)
    (hvertical : ratio ^ verticalDepth < 1) :
    deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) ratio =
      deriv (centeredHorizontalFactor tailDepth (fun index => (digits index).1)) ratio * exponent *
        (centeredHorizontalFactor tailDepth (fun index => (digits index).1) ratio) ^ (exponent - 1) -
      exponent * (((verticalDepth : ℝ) - exponent * horizontalDepth) *
        ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth - 1) *
        centeredTailFactor tailDepth (fun index => (digits index).2) ratio +
        ratio ^ ((verticalDepth : ℝ) - exponent * horizontalDepth) *
          deriv (centeredTailFactor tailDepth (fun index => (digits index).2)) ratio) +
      centeredRemainderFirst exponent horizontalDepth verticalDepth tailDepth
        (fun index => (digits index).2) ratio := by
  rw [(centeredNormalizedResidual_hasDerivAt exponent horizontalDepth verticalDepth tailDepth
    digits hpositive hless hhorizontal hvertical).deriv,
    (centeredHorizontalFactor_hasDerivAt tailDepth (fun index => (digits index).1) hpositive hless).deriv,
    (centeredTailFactor_hasDerivAt tailDepth (fun index => (digits index).2) hpositive hless).deriv]
  ring

theorem centered_root_mem_intersection (exponent : ℝ)
    (horizontalDepth verticalDepth tailDepth : ℕ) (digits : ℕ → Bool × Bool)
    {ratio : ℝ} (hpositive : 0 < ratio) (hless : ratio < 1)
    (hzero : centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits ratio = 0) :
    centeredCylinder ratio horizontalDepth verticalDepth tailDepth
      (address ratio (fun index => (digits index).1), address ratio (fun index => (digits index).2)) ∈
        intersection exponent ratio := by
  have hcoordinates := centeredCylinder_mem_dust hpositive.le hless horizontalDepth verticalDepth tailDepth
    (show (address ratio (fun index => (digits index).1), address ratio (fun index => (digits index).2)) ∈
      Last.cantorDust ratio from ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩)
  have hidentity := centeredNormalizedResidual_actual exponent horizontalDepth verticalDepth tailDepth digits hpositive hless
  rw [hzero] at hidentity
  have hresidual := (div_eq_zero_iff.mp hidentity.symm).resolve_right
    (ne_of_gt (Real.rpow_pos_of_pos hpositive (exponent * (horizontalDepth : ℝ))))
  exact ⟨hcoordinates.1, hcoordinates.2, sub_eq_zero.mp hresidual⟩

end LambdaCantor.AE
