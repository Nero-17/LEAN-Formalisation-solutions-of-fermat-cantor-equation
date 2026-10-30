import LambdaCantor.First.RootsKernelNeighborhoods
import LambdaCantor.First.RootsConvergence

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

theorem prefixNeighborhood_antitone (selected : Set (ℕ → Bool × Bool)) :
    Antitone (prefixNeighborhood selected) := by
  intro smaller larger ordered digits member
  obtain ⟨representative, representative_mem, agreement⟩ := member
  exact ⟨representative, representative_mem,
    fun index before => agreement index (before.trans_le ordered)⟩

/-- The actual mass lost by successive prefix neighborhoods is summable,
without any quantitative regularity premise on the selected address set. -/
theorem prefixNeighborhood_deleted_mass_summable (selected : Set (ℕ → Bool × Bool)) :
    Summable (fun depth => pairedAddressMeasure.real (prefixNeighborhood selected depth) -
      pairedAddressMeasure.real (prefixNeighborhood selected (depth + 1))) := by
  apply summable_deleted_mass
  · intro depth
    exact ENNReal.toReal_nonneg
  · intro smaller larger ordered
    exact measureReal_mono (prefixNeighborhood_antitone selected ordered)

end LambdaCantor.First.Roots
