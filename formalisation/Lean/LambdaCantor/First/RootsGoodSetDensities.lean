import LambdaCantor.First.RootsExternalFourierDensity
import LambdaCantor.First.RootsGoodSets
import LambdaCantor.First.RootsKernelSumDensity

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

/-- The precisely isolated classical converse supplies actual projected
L1/L2 densities at every point of each genuine compact energy sublevel. -/
theorem rootSobolevGoodSet_projected_density
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ)
    (representative : ℕ → Bool × Bool)
    (member : representative ∈ rootSobolevGoodSet data orderIndex bound) :
    LinearRegularity.HasL2Density
      (pairedAddressMeasure.map (projectedRootModel (rootFibreState data representative))) := by
  apply hasL2Density_of_weighted_energy _
    (projectedRootModel_compact_support
      (show 0 ≤ (rootFibreState data representative).1 by
        change 0 ≤ data.root representative
        linarith [data.lower_gt_quarter, (data.root_in_band representative).1])
      (show (rootFibreState data representative).1 < 1 by
        change data.root representative < 1
        linarith [data.upper_lt_half, (data.root_in_band representative).2]))
    (1 / ((orderIndex : ℝ) + 1)) (by positivity)
  exact ne_top_of_le_ne_top (by simp) member

/-- Actual finite-depth approximations on the compact good sets have genuine
L1/L2 densities. The only external input is the separately named classical
compact-measure Fourier converse, not a root-fibres theorem. -/
theorem rootSobolevGoodSet_kernel_sum_density
    {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound depth : ℕ) :
    LinearRegularity.HasL2Density
      ((pairedAddressMeasure.restrict (prefixNeighborhood (rootSobolevGoodSet data orderIndex bound) depth)).map
        (selectedRootKernel data (rootSobolevGoodSet data orderIndex bound) depth)) := by
  apply selectedRootKernel_law_hasL2Density
  intro representative member
  exact rootSobolevGoodSet_projected_density data orderIndex bound representative member

end LambdaCantor.First.Roots

