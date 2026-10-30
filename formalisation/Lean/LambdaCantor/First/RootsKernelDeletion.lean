import LambdaCantor.First.RootsNeighborhoodMass

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

def deletedRootKernelLaw {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) : Measure ℝ :=
  (pairedAddressMeasure.restrict
    (prefixNeighborhood selected depth \ prefixNeighborhood selected (depth + 1))).map
    (selectedRootKernel data selected depth)

/-- Before replacing surviving parent kernels by child kernels, deletion is
an exact decomposition of the actual finite-prefix law into positive measures. -/
theorem selectedRootKernel_law_retained_add_deleted {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) :
    (pairedAddressMeasure.restrict (prefixNeighborhood selected depth)).map
      (selectedRootKernel data selected depth) =
    (pairedAddressMeasure.restrict (prefixNeighborhood selected (depth + 1))).map
      (selectedRootKernel data selected depth) + deletedRootKernelLaw data selected depth := by
  have decomposition := Measure.restrict_inter_add_sdiff (μ := pairedAddressMeasure)
    (prefixNeighborhood selected depth) (measurableSet_prefixNeighborhood selected (depth + 1))
  rw [Set.inter_eq_right.mpr (prefixNeighborhood_antitone selected (Nat.le_succ depth))] at decomposition
  rw [← decomposition, Measure.map_add _ _
    (continuous_selectedRootKernel data selected depth).measurable]
  rfl

theorem deletedRootKernelLaw_mass {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) (depth : ℕ) :
    (deletedRootKernelLaw data selected depth).real Set.univ =
      pairedAddressMeasure.real (prefixNeighborhood selected depth) -
        pairedAddressMeasure.real (prefixNeighborhood selected (depth + 1)) := by
  unfold deletedRootKernelLaw
  simp only [measureReal_def, Measure.map_apply
    (continuous_selectedRootKernel data selected depth).measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ]
  exact measureReal_sdiff (prefixNeighborhood_antitone selected (Nat.le_succ depth))
    (measurableSet_prefixNeighborhood selected (depth + 1))

theorem deletedRootKernelLaw_mass_summable {exponent : ℝ} (data : RootFibreData exponent)
    (selected : Set (ℕ → Bool × Bool)) :
    Summable (fun depth => (deletedRootKernelLaw data selected depth).real Set.univ) := by
  simpa only [deletedRootKernelLaw_mass] using prefixNeighborhood_deleted_mass_summable selected

end LambdaCantor.First.Roots

