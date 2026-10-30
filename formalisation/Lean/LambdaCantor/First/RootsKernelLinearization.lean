import LambdaCantor.First.RootsPowerLinearization
import LambdaCantor.First.RootsRootDisplacement
import LambdaCantor.First.RootsCylinderDifferences

noncomputable section
namespace LambdaCantor.First.Roots

theorem cylinderCoordinate_shared_prefix_difference {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (word : ℕ → Bool) (length depth : ℕ) (left right : ℕ → Bool)
    (agreement : ∀ index < depth, left index = right index) :
    cylinderCoordinate word length right ratio - cylinderCoordinate word length left ratio =
      ratio ^ (length + depth) *
        (address ratio (fun index => right (index + depth)) -
         address ratio (fun index => left (index + depth))) := by
  have difference := address_shared_prefix_difference nonnegative less_one right left depth
    (fun index index_lt => (agreement index index_lt).symm)
  unfold cylinderCoordinate
  rw [pow_add]
  calc
    _ = ratio ^ length * (address ratio right - address ratio left) := by ring
    _ = _ := by rw [difference]; ring

/-- The complete linear term in the manuscript kernel, before division by
the actual residual derivative at the representative root. -/
def rootKernelLinearTerm {exponent : ℝ} (data : RootFibreData exponent)
    (representative digits : ℕ → Bool × Bool) (depth : ℕ) (ratio : ℝ) : ℝ :=
  exponent * cylinderCoordinate data.leftWord data.leftLength
      (fun index => (representative index).1) ratio ^ (exponent - 1) * ratio ^ (data.leftLength + depth) *
      (address ratio (fun index => (digits (index + depth)).1) -
       address ratio (fun index => (representative (index + depth)).1)) +
    exponent * cylinderCoordinate data.rightWord data.rightLength
      (fun index => (representative index).2) ratio ^ (exponent - 1) * ratio ^ (data.rightLength + depth) *
      (address ratio (fun index => (digits (index + depth)).2) -
       address ratio (fun index => (representative (index + depth)).2))

def rootKernelValue {exponent : ℝ} (data : RootFibreData exponent)
    (representative digits : ℕ → Bool × Bool) (depth : ℕ) : ℝ :=
  data.root representative - rootKernelLinearTerm data representative digits depth (data.root representative) /
    deriv (cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative)
      (data.root representative)

/-- Genuine fixed-parameter Taylor cancellation for the actual two cylinder
coordinates. The linear term is precisely the one in the complete frozen kernel. -/
theorem rootFibreData_kernel_residual_linearization {exponent : ℝ} (data : RootFibreData exponent) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (representative digits : ℕ → Bool × Bool) (depth : ℕ) (ratio : ℝ),
        ratio ∈ Set.Icc data.lower data.upper →
        (∀ index < depth, representative index = digits index) →
        |cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength digits ratio -
          cylinderResidual exponent data.leftWord data.rightWord data.leftLength data.rightLength representative ratio -
          rootKernelLinearTerm data representative digits depth ratio| ≤ constant * (ratio ^ depth) ^ 2 := by
  obtain ⟨lowerCoordinate, lower_positive, coordinate_lower⟩ := rootFibreData_uniform_positive_coordinates data
  let coefficient : ℝ := |exponent| * (|exponent - 1| * max 1 (lowerCoordinate ^ (exponent - 2)))
  have coefficient_nonnegative : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  refine ⟨2 * coefficient, by positivity, ?_⟩
  intro representative digits depth ratio in_band agreement
  have ratio_nonnegative : 0 ≤ ratio := by linarith [data.lower_gt_quarter, in_band.1]
  have ratio_lt_one : ratio < 1 := by linarith [data.upper_lt_half, in_band.2]
  have coordinate_upper (word : ℕ → Bool) (length : ℕ) (tail : ℕ → Bool) :
      cylinderCoordinate word length tail ratio ≤ 1 := by
    unfold cylinderCoordinate
    rw [← cylinder_address ratio_nonnegative ratio_lt_one word length tail]
    exact address_le_one ratio_nonnegative ratio_lt_one _
  have coordinate_estimate (word : ℕ → Bool) (length : ℕ) (coordinate : Bool × Bool → Bool)
      (representative_lower : lowerCoordinate ≤ cylinderCoordinate word length
        (fun index => coordinate (representative index)) ratio)
      (digits_lower : lowerCoordinate ≤ cylinderCoordinate word length
        (fun index => coordinate (digits index)) ratio) :
      |cylinderCoordinate word length (fun index => coordinate (digits index)) ratio ^ exponent -
        cylinderCoordinate word length (fun index => coordinate (representative index)) ratio ^ exponent -
        exponent * cylinderCoordinate word length (fun index => coordinate (representative index)) ratio ^ (exponent - 1) *
          ratio ^ (length + depth) *
          (address ratio (fun index => coordinate (digits (index + depth))) -
           address ratio (fun index => coordinate (representative (index + depth))))| ≤
        coefficient * (ratio ^ depth) ^ 2 := by
    have power_estimate := rpow_linearization_positive_band (exponent := exponent) lower_positive
      ⟨representative_lower, coordinate_upper _ _ _⟩ ⟨digits_lower, coordinate_upper _ _ _⟩
    have difference_bound := cylinderCoordinate_shared_prefix_bound ratio_nonnegative ratio_lt_one word length depth
      (fun index => coordinate (digits index)) (fun index => coordinate (representative index))
      (fun index index_lt => congrArg coordinate (agreement index index_lt).symm)
    have scaled_bound := mul_le_mul_of_nonneg_right
      (pow_le_one₀ ratio_nonnegative ratio_lt_one.le : ratio ^ length ≤ 1)
      (pow_nonneg ratio_nonnegative depth)
    have difference_le : |cylinderCoordinate word length (fun index => coordinate (digits index)) ratio -
        cylinderCoordinate word length (fun index => coordinate (representative index)) ratio| ≤ ratio ^ depth :=
      difference_bound.trans (by simpa only [one_mul] using scaled_bound)
    have square_bound := (sq_le_sq₀ (abs_nonneg _) (pow_nonneg ratio_nonnegative depth)).mpr difference_le
    have estimate := power_estimate.trans (mul_le_mul_of_nonneg_left square_bound coefficient_nonnegative)
    rw [cylinderCoordinate_shared_prefix_difference ratio_nonnegative ratio_lt_one word length depth
      (fun index => coordinate (representative index)) (fun index => coordinate (digits index))
      (fun index index_lt => congrArg coordinate (agreement index index_lt))] at estimate
    simpa only [mul_assoc, coefficient] using estimate
  have left_estimate := coordinate_estimate data.leftWord data.leftLength Prod.fst
    (coordinate_lower representative ratio in_band).1 (coordinate_lower digits ratio in_band).1
  have right_estimate := coordinate_estimate data.rightWord data.rightLength Prod.snd
    (coordinate_lower representative ratio in_band).2 (coordinate_lower digits ratio in_band).2
  unfold cylinderResidual rootKernelLinearTerm
  have identity : ∀ a b c d e f : ℝ,
      (a + b - 1) - (c + d - 1) - (e + f) = (a - c - e) + (b - d - f) := by
    intros
    ring
  rw [identity]
  exact (abs_add_le _ _).trans (by linarith)

end LambdaCantor.First.Roots
