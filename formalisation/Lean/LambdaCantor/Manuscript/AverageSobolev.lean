import LambdaCantor.AE.CanonicalSobolevEnergy
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace LambdaCantor.Manuscript

/-- Lemma 4.7 with the canonical Fourier weight `(1+|frequency|^2)^regularity`.
The extended parameter integral is finite on every compact subset. The same
norm is realized by an actual nonnegative L1 and L2 density almost everywhere.
-/
theorem average_sobolev {lower upper regularity : ℝ}
    (lower_above_three_eighths : 3/8 < lower) (ordered : lower ≤ upper)
    (upper_below_half : upper < 1/2) (regularity_positive : 0 < regularity)
    (regularity_range : 2*regularity <
      2*Real.log (8/3 : ℝ)/Real.log (upper/lower^3)-1) :
    (∀ compact : Set ℝ, compact ⊆ Set.Ioo lower upper → IsCompact compact →
      (∫⁻ ratio in compact, AE.canonicalSobolevEnergy ratio regularity) < ⊤ ∧
      IntegrableOn (fun ratio => (AE.canonicalSobolevEnergy ratio regularity).toReal) compact volume) ∧
    (∀ᵐ ratio : ℝ, ratio ∈ Set.Ioo lower upper →
      AE.HasCanonicalSobolevDensity (AE.selfConvolutionProbability ratio) regularity) := by
  have lower_positive : 0 < lower := by linarith
  refine ⟨?_, AE.ae_hasCanonicalSobolevDensity_on_interval lower_positive ordered upper_below_half
    regularity_positive.le regularity_range⟩
  intro compact contained compactness
  exact ⟨AE.lintegral_canonicalSobolevEnergy_compact_subset_lt_top lower_positive ordered
      upper_below_half regularity_positive.le regularity_range compact contained compactness,
    AE.integrableOn_canonicalSobolevEnergy_compact_subset lower_positive ordered upper_below_half
      regularity_positive.le regularity_range compact contained compactness⟩

end LambdaCantor.Manuscript

#print axioms LambdaCantor.Manuscript.average_sobolev
