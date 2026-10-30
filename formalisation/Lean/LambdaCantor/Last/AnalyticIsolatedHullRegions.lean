import LambdaCantor.Last.AnalyticIsolatedBoundaryShadow
import LambdaCantor.Last.AnalyticIsolatedTopology

noncomputable section
namespace LambdaCantor.Last

structure OrderedActualChildHulls (lower upper : Bool × Bool → ℝ) : Prop where
  lower_first : lower (false,false) ≤ lower (true,false)
  lower_middle : lower (true,false) ≤ lower (false,true)
  lower_last : lower (false,true) ≤ lower (true,true)
  upper_first : upper (false,false) ≤ upper (true,false)
  upper_middle : upper (true,false) ≤ upper (false,true)
  upper_last : upper (false,true) ≤ upper (true,true)

def ActualExclusiveRegion (lower upper : Bool × Bool → ℝ) (level : ℝ)
    (digit : Bool × Bool) : Prop :=
  match digit with
  | (false,false) => level ≤ lower (true,false)
  | (true,false) => upper (false,false) ≤ level ∧ level ≤ lower (false,true)
  | (false,true) => upper (true,false) ≤ level ∧ level ≤ lower (true,true)
  | (true,true) => upper (false,true) ≤ level

theorem actual_exclusive_of_unique_closed_child
    (lower upper : Bool × Bool → ℝ) (ordered : OrderedActualChildHulls lower upper)
    (level : ℝ) (digit : Bool × Bool) (inside : level ∈ Set.Icc (lower digit) (upper digit))
    (unique : ∀ other : Bool × Bool, other ≠ digit →
      level ∉ Set.Icc (lower other) (upper other)) :
    ActualExclusiveRegion lower upper level digit := by
  rcases digit with ⟨first, second⟩
  cases first <;> cases second
  · change level ≤ lower (true,false)
    by_contra not_lower
    exact unique (true,false) (by decide)
      ⟨(lt_of_not_ge not_lower).le, inside.2.trans ordered.upper_first⟩
  · change upper (true,false) ≤ level ∧ level ≤ lower (true,true)
    constructor
    · by_contra not_upper
      exact unique (true,false) (by decide)
        ⟨ordered.lower_middle.trans inside.1, (lt_of_not_ge not_upper).le⟩
    · by_contra not_lower
      exact unique (true,true) (by decide)
        ⟨(lt_of_not_ge not_lower).le, inside.2.trans ordered.upper_last⟩
  · change upper (false,false) ≤ level ∧ level ≤ lower (false,true)
    constructor
    · by_contra not_upper
      exact unique (false,false) (by decide)
        ⟨ordered.lower_first.trans inside.1, (lt_of_not_ge not_upper).le⟩
    · by_contra not_lower
      exact unique (false,true) (by decide)
        ⟨(lt_of_not_ge not_lower).le, inside.2.trans ordered.upper_middle⟩
  · change upper (false,true) ≤ level
    by_contra not_upper
    exact unique (false,true) (by decide)
      ⟨ordered.lower_last.trans inside.1, (lt_of_not_ge not_upper).le⟩

def boundaryAffineLower (ratio : ℝ) : Bool × Bool → ℝ
  | (false,false) => 0
  | (true,false) => 1-ratio
  | (false,true) => 1/2+ratio
  | (true,true) => 3/2

def boundaryAffineUpper (ratio : ℝ) : Bool × Bool → ℝ
  | (false,false) => 1/2+ratio
  | (true,false) => 3/2
  | (false,true) => 1+2*ratio
  | (true,true) => 2+ratio

/-- The actual child-hull restriction yields exactly the critical-phase
approximate exclusive sets, with twice the endpoint Taylor-error bound.
All quantities are actual normalized levels and endpoints, not an assumed
address classification. -/
theorem boundary_approx_exclusive_of_actual_hulls
    {ratio actualLevel tangentLevel error : ℝ}
    (lower upper : Bool × Bool → ℝ) (ordered : OrderedActualChildHulls lower upper)
    (digit : Bool × Bool)
    (inside : actualLevel ∈ Set.Icc (lower digit) (upper digit))
    (unique : ∀ other : Bool × Bool, other ≠ digit →
      actualLevel ∉ Set.Icc (lower other) (upper other))
    (lower_error : ∀ child, |lower child-boundaryAffineLower ratio child| ≤ error)
    (upper_error : ∀ child, |upper child-boundaryAffineUpper ratio child| ≤ error)
    (level_error : |tangentLevel-actualLevel| ≤ error) :
    BoundaryApproxExclusive ratio tangentLevel (2*error) digit := by
  have exclusive := actual_exclusive_of_unique_closed_child lower upper ordered actualLevel digit inside unique
  have level_bounds := abs_le.mp level_error
  have lower10 := abs_le.mp (lower_error (true,false))
  have lower01 := abs_le.mp (lower_error (false,true))
  have lower11 := abs_le.mp (lower_error (true,true))
  have upper00 := abs_le.mp (upper_error (false,false))
  have upper10 := abs_le.mp (upper_error (true,false))
  have upper01 := abs_le.mp (upper_error (false,true))
  rcases digit with ⟨first, second⟩
  cases first <;> cases second <;>
    simp only [ActualExclusiveRegion, BoundaryApproxExclusive, boundaryAffineLower,
      boundaryAffineUpper, abs_le] at *
  all_goals first | constructor <;> linarith | linarith

end LambdaCantor.Last
