import LambdaCantor.Last.AnalyticIsolatedHullRegions
import LambdaCantor.Last.AnalyticIsolatedApproximateOrbit

noncomputable section
namespace LambdaCantor.Last

theorem affine_actual_children_ordered {ratio slope error : ℝ}
    (outer_room : 2*error ≤ 1-ratio) (middle_room : 2*error ≤ (slope-1)*(1-ratio))
    (lower upper : Bool × Bool → ℝ)
    (lower_error : ∀ digit, |lower digit-affineChildOffset ratio slope digit| ≤ error)
    (upper_error : ∀ digit, |upper digit-(affineChildOffset ratio slope digit+ratio*(1+slope))| ≤ error) :
    OrderedActualChildHulls lower upper := by
  have order_pair : ∀ first second left right : ℝ,
      |first-left| ≤ error → |second-right| ≤ error → 2*error ≤ right-left → first ≤ second := by
    intro first second left right first_bound second_bound separation
    have first_bounds := abs_le.mp first_bound
    have second_bounds := abs_le.mp second_bound
    linarith
  constructor
  · apply order_pair _ _ _ _ (lower_error (false,false)) (lower_error (true,false))
    dsimp [affineChildOffset]
    nlinarith
  · apply order_pair _ _ _ _ (lower_error (true,false)) (lower_error (false,true))
    dsimp [affineChildOffset]
    nlinarith
  · apply order_pair _ _ _ _ (lower_error (false,true)) (lower_error (true,true))
    dsimp [affineChildOffset]
    nlinarith
  · apply order_pair _ _ _ _ (upper_error (false,false)) (upper_error (true,false))
    dsimp [affineChildOffset]
    nlinarith
  · apply order_pair _ _ _ _ (upper_error (true,false)) (upper_error (false,true))
    dsimp [affineChildOffset]
    nlinarith
  · apply order_pair _ _ _ _ (upper_error (false,true)) (upper_error (true,true))
    dsimp [affineChildOffset]
    nlinarith

theorem approx_affine_exclusive_of_actual_hulls
    {ratio slope actualLevel tangentLevel error : ℝ}
    (lower upper : Bool × Bool → ℝ) (ordered : OrderedActualChildHulls lower upper)
    (digit : Bool × Bool) (inside : actualLevel ∈ Set.Icc (lower digit) (upper digit))
    (unique : ∀ other : Bool × Bool, other ≠ digit → actualLevel ∉ Set.Icc (lower other) (upper other))
    (lower_error : ∀ child, |lower child-affineChildOffset ratio slope child| ≤ error)
    (upper_error : ∀ child, |upper child-(affineChildOffset ratio slope child+ratio*(1+slope))| ≤ error)
    (level_error : |tangentLevel-actualLevel| ≤ error) :
    ApproxAffineExclusiveRegion ratio slope tangentLevel (2*error) digit := by
  have exclusive := actual_exclusive_of_unique_closed_child lower upper ordered actualLevel digit inside unique
  have level_bounds := abs_le.mp level_error
  have lower10 := abs_le.mp (lower_error (true,false))
  have lower01 := abs_le.mp (lower_error (false,true))
  have lower11 := abs_le.mp (lower_error (true,true))
  have upper00 := abs_le.mp (upper_error (false,false))
  have upper10 := abs_le.mp (upper_error (true,false))
  have upper01 := abs_le.mp (upper_error (false,true))
  simp only [affineChildOffset, Bool.false_eq_true, if_false, if_true, mul_zero,
    zero_add, add_zero, mul_one] at lower10 lower01 lower11 upper00 upper10 upper01
  rcases digit with ⟨first, second⟩
  cases first <;> cases second <;>
    simp only [ActualExclusiveRegion, ApproxAffineExclusiveRegion] at *
  all_goals first | constructor <;> nlinarith | nlinarith

end LambdaCantor.Last
