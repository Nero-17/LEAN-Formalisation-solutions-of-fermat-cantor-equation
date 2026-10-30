import LambdaCantor.AE.NewtonMixture
import LambdaCantor.AE.FiniteDensityMixture

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LambdaCantor.AE

/-- The finite sum of the actual kernel densities is a nonnegative element
of the precise L1 space used for convergence, and its law is the actual
paired-source Newton observable. -/
theorem actual_newton_mixture_L1 (depth : ℕ)
    (kernels : (Fin depth → Bool × Bool) → FrozenNewtonKernel)
    (density : (Fin depth → Bool × Bool) → ℝ → ℝ)
    (integrable : ∀ word, Integrable (density word))
    (nonnegative : ∀ word, ∀ᵐ value : ℝ, 0 ≤ density word value)
    (density_laws : ∀ word, (kernels word).law =
      volume.withDensity (fun value => ENNReal.ofReal (density word value))) :
    ∃ mixture : Lp ℝ 1 volume, 0 ≤ mixture ∧
      (mixture : ℝ → ℝ) =ᵐ[volume]
        (fun value => ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*density word value) ∧
      First.Roots.pairedAddressMeasure.map (newtonMixtureObservable depth kernels) =
        volume.withDensity (fun value => ENNReal.ofReal (mixture value)) := by
  obtain ⟨mixture, mixture_nonnegative, representative, mixture_law⟩ :=
    finite_density_mixture_L1 (fun _word : Fin depth → Bool × Bool => (1/4 : ℝ)^depth)
      density (fun _ => by positivity) integrable nonnegative
  refine ⟨mixture, mixture_nonnegative, representative, ?_⟩
  rw [newtonMixtureObservable_law, mixture_law]
  apply Finset.sum_congr rfl
  intro word _
  have weight : ENNReal.ofReal ((1/4 : ℝ)^depth) = (4 : ℝ≥0∞)⁻¹^depth := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/4)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  rw [weight, density_laws word]

end LambdaCantor.AE
