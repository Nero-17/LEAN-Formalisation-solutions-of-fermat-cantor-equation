/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import LambdaCantor.AE.MathlibSupport.Analysis.Convolution
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The Fourier transform of the convolution

In this file we calculate the Fourier transform of a convolution.

## Main definitions
* `SchwartzMap.convolution`: The convolution on Schwartz functions is defined via the Fourier
  transform.

## Main statements
* `Real.fourier_bilin_convolution_eq`: The Fourier transform of a convolution is the bilinear map
  applied to the Fourier transform of the functions.
* `Real.fourier_smul_convolution_eq`: Variant for scalar multiplication.
* `Real.fourier_mul_convolution_eq`: Variant for multiplication.
* `SchwartzMap.fourier_convolution`: The Fourier transform of the Schwartz convolution is given by
  the pairing of the Fourier transformed Schwartz functions.
* `SchwartzMap.convolution_apply`: The Schwartz function convolution coincides with the convolution
  for functions.

-/

@[expose] public section

variable {𝕜 R E F F₁ F₂ F₃ : Type*}

namespace Real

open MeasureTheory Convolution

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] [NormedAddCommGroup F₃]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂] [NormedSpace 𝕜 F₃]

/-- The norm of the integrand of the convolution is integrable if the functions are integrable. -/
theorem integrable_prod_sub (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) :
    Integrable (fun (p : E × E) ↦ ‖B‖ * (‖f₁ (p.1 - p.2)‖ * ‖f₂ p.2‖)) (volume.prod volume) := by
  simpa [mul_comm] using (hf₂.norm.convolution_integrand (.mul ℝ ℝ) hf₁.norm).const_mul ‖B‖

open FourierTransform

variable [NormedSpace ℂ F₃]

/-- Calculate the Fourier transform of the convolution as a symmetric integral. -/
theorem fourier_bilin_convolution_eq_integral (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := calc
  _ = 𝓕 (f₂ ⋆[B.flip] f₁) ξ := by
    rw [convolution_flip]
  _ = ∫ x, 𝐞 (-inner ℝ x ξ) • ∫ y, B (f₁ (x - y)) (f₂ y) := by rfl
  _ = ∫ x, ∫ y, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
    congr
    ext x
    simp_rw [Circle.smul_def, integral_smul]
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ x ξ) • B (f₁ (x - y)) (f₂ y) := by
    refine integral_integral_swap ?_
    have hB := hf₂.convolution_integrand B.flip hf₁
    refine hB.mono ?_ ?_
    · exact continuous_fourierChar.comp (by fun_prop) |>.aestronglyMeasurable.smul
        hB.aestronglyMeasurable
    · filter_upwards with ⟨x, y⟩ using by simp
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) := by
    congr
    ext y
    -- Linear change of variables
    convert! integral_sub_right_eq_self _ y (μ := volume)
    congr
    simp

variable [CompleteSpace F₁] [CompleteSpace F₂] [CompleteSpace F₃]
  [NormedSpace ℂ F₁] [NormedSpace ℂ F₂]

open ContinuousLinearMap

/-- The Fourier transform of the convolution is given by the bilinear map applied to the Fourier
transform of the individual functions. -/
theorem fourier_bilin_convolution_eq (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃) {f₁ : E → F₁} {f₂ : E → F₂}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[B] f₂) ξ = B (𝓕 f₁ ξ) (𝓕 f₂ ξ) := calc
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ (y + x) ξ) • B (f₁ x) (f₂ y) :=
    fourier_bilin_convolution_eq_integral B hf₁ hf₂ _
  _ = ∫ y, ∫ x, 𝐞 (-inner ℝ y ξ) • 𝐞 (-inner ℝ x ξ) • B (f₁ x) (f₂ y) := by
    simp_rw [inner_add_left, neg_add, AddChar.map_add_eq_mul, smul_smul]
  _ = ∫ y, (∫ x, B (𝐞 (-inner ℝ x ξ) • f₁ x)) (𝐞 (-inner ℝ y ξ) • f₂ y) := by
    congr with y
    have : Integrable (fun x ↦ (𝐞 (-inner ℝ x ξ) : ℂ) • B (f₁ x)) volume := by
      simpa [Circle.smul_def] using
        (Real.fourierIntegral_convergent_iff ξ).2 (B.integrable_comp hf₁)
    simp [Circle.smul_def, MeasureTheory.integral_smul, integral_apply this (f₂ y)]
  _ = B (∫ x, 𝐞 (-inner ℝ x ξ) • f₁ x) (∫ y, 𝐞 (-inner ℝ y ξ) • f₂ y) := by
    rw [← integral_comp_comm _ (by simpa using hf₂), ← integral_comp_comm _ (by simpa using hf₁)]

/-- The Fourier transform of the convolution is given by the multiplication of the Fourier transform
of the individual functions.

Version for scalar multiplication. -/
theorem fourier_smul_convolution_eq {f₁ : E → ℂ} {f₂ : E → F₁}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[lsmul ℂ ℂ] f₂) ξ = (𝓕 f₁ ξ) • (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (lsmul ℂ ℂ) hf₁ hf₂ ξ

variable [NormedRing R] [NormedSpace ℂ R] [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
  [CompleteSpace R]

/-- The Fourier transform of the convolution is given by the multiplication of the Fourier transform
of the individual functions.

Version for multiplication. -/
theorem fourier_mul_convolution_eq {f₁ : E → R} {f₂ : E → R}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂) (ξ : E) :
    𝓕 (f₁ ⋆[mul ℂ R] f₂) ξ = (𝓕 f₁ ξ) * (𝓕 f₂ ξ) :=
  fourier_bilin_convolution_eq (mul ℂ R) hf₁ hf₂ ξ

end Real


/- Source provenance: Mathlib/Analysis/Fourier/Convolution.lean SHA256 013748C887AB3AEEDC75134386E0ECE06EA636933DE97AEFBC6655CBA4012C30. Exact initial Real namespace retained; later Schwartz namespace omitted. Imports changed to the local identical Convolution copy, cached FourierTransform, and Haar.Unique for the standard negation-invariance instance; copyright/license retained. -/
