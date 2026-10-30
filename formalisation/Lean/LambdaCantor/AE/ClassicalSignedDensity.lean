import LambdaCantor.AE.ExternalPlancherelDensity

noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

namespace LambdaCantor.AE

/-- Real signed inverse Plancherel, specialized from the registered general
complex L1 converse. No positivity, parameter, or Cantor hypothesis occurs. -/
theorem classical_signed_density_memLp_and_norm_bound {density : ℝ → ℝ}
    (integrable : Integrable density)
    (fourier : MemLp (𝓕 (fun value => (density value : ℂ))) 2 volume) :
    MemLp density 2 volume ∧
      (∫ value : ℝ, |density value|^2) ≤
        ∫ frequency : ℝ, ‖𝓕 (fun value => (density value : ℂ)) frequency‖^2 := by
  have complex_integrable : Integrable (fun value => (density value : ℂ)) :=
    integrable.mono
      (Complex.continuous_ofReal.comp_aestronglyMeasurable integrable.aestronglyMeasurable)
      (Eventually.of_forall (fun value => by simp))
  obtain ⟨complex_memLp, identity⟩ :=
    ExternalPlancherel.complex_L1_of_fourier_L2 _ complex_integrable fourier
  have real_norm : MemLp (fun value => ‖density value‖) 2 volume := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using complex_memLp.norm
  refine ⟨(memLp_norm_iff integrable.aestronglyMeasurable).mp real_norm, ?_⟩
  simpa only [Complex.norm_real, Real.norm_eq_abs] using identity.le

end LambdaCantor.AE
