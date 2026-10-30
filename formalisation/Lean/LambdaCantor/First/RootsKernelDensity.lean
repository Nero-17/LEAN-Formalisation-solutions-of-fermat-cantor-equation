import LambdaCantor.First.RootsKernelState
import LambdaCantor.First.RootsAffineDensity

noncomputable section
open MeasureTheory
namespace LambdaCantor.First.Roots

/-- A genuine L2 density for the projected state law transports to the actual
complete frozen kernel. Its density is the explicit affine change of variables. -/
theorem completeRootKernelLaw_hasL2Density {exponent : ℝ} (data : RootFibreData exponent)
    (representative : ℕ → Bool × Bool) (depth : ℕ)
    (projected_density : LinearRegularity.HasL2Density
      (pairedAddressMeasure.map (projectedRootModel (rootFibreState data representative)))) :
    LinearRegularity.HasL2Density (completeRootKernelLaw data representative depth) := by
  rw [completeRootKernelLaw_rootModel]
  convert hasL2Density_affine projected_density
    (data.root representative + rootKernelHorizontal data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).1) +
      rootKernelVertical data representative depth *
      address (data.root representative) (fun index => (representative (index + depth)).2))
    (-rootKernelVertical data representative depth)
    (neg_ne_zero.mpr (rootKernelVertical_ne_zero data representative depth)) using 1
  congr 1
  funext value
  ring

end LambdaCantor.First.Roots
