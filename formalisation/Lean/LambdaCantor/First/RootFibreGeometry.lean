import LambdaCantor.First.RootFibreTopology
import LambdaCantor.First.RootsIncidence

noncomputable section
namespace LambdaCantor.First.Roots

theorem cylinderCoordinate_mem_cantorSet {ratio : ℝ}
    (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (word : ℕ → Bool) (length : ℕ) (tail : ℕ → Bool) :
    cylinderCoordinate word length tail ratio ∈ cantorSet ratio := by
  exact ⟨cylinderDigits word length tail,
    cylinder_address nonnegative less_one word length tail⟩

/-- The concrete root data supplies actual points of the Cantor intersection. -/
theorem rootFibreData_point_mem_intersection {exponent : ℝ}
    (data : RootFibreData exponent) (digits : ℕ → Bool × Bool) :
    (cylinderCoordinate data.leftWord data.leftLength (fun index => (digits index).1)
        (data.root digits),
      cylinderCoordinate data.rightWord data.rightLength (fun index => (digits index).2)
        (data.root digits)) ∈ intersection exponent (data.root digits) := by
  have nonnegative : 0 ≤ data.root digits := by
    linarith [data.lower_gt_quarter, (data.root_in_band digits).1]
  have less_one : data.root digits < 1 := by
    linarith [data.upper_lt_half, (data.root_in_band digits).2]
  refine ⟨cylinderCoordinate_mem_cantorSet nonnegative less_one _ _ _,
    cylinderCoordinate_mem_cantorSet nonnegative less_one _ _ _, ?_⟩
  have zero := (data.unique_root digits (data.root digits) (data.root_in_band digits)).mpr rfl
  exact sub_eq_zero.mp zero

end LambdaCantor.First.Roots
