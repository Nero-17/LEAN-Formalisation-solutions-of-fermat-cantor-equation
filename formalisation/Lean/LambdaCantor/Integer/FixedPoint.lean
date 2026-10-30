import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace LambdaCantor.Integer

/-- Outward nonnegative interval endpoints on a fixed integer lattice. -/
structure NatInterval where
  lower : ℕ
  upper : ℕ
  deriving DecidableEq

def NatInterval.Encloses (scale : ℕ) (bounds : NatInterval) (value : ℝ) : Prop :=
  (bounds.lower : ℝ) ≤ (scale : ℝ)*value ∧ (scale : ℝ)*value ≤ bounds.upper

def NatInterval.add (first second : NatInterval) : NatInterval :=
  ⟨first.lower+second.lower,first.upper+second.upper⟩

def NatInterval.divide (bounds : NatInterval) (denominator : ℕ) : NatInterval :=
  ⟨bounds.lower/denominator,bounds.upper/denominator+1⟩

/-- Three factors, rounded once. This keeps atanh powers on the fixed lattice. -/
def NatInterval.mulThree (scale : ℕ) (first second third : NatInterval) : NatInterval :=
  ⟨first.lower*second.lower*third.lower/(scale*scale),
    first.upper*second.upper*third.upper/(scale*scale)+1⟩

theorem nat_division_outward (numerator denominator : ℕ) (positive : 0 < denominator) :
    ((numerator/denominator : ℕ) : ℝ)*denominator ≤ numerator ∧
      (numerator : ℝ) ≤ ((numerator/denominator+1 : ℕ) : ℝ)*denominator := by
  constructor
  · exact_mod_cast Nat.div_mul_le_self numerator denominator
  · have decomposition := Nat.mod_add_div numerator denominator
    have remainder := Nat.mod_lt numerator positive
    have bound : numerator ≤ (numerator/denominator+1)*denominator := by nlinarith
    exact_mod_cast bound

theorem NatInterval.nonnegative {scale : ℕ} (positive : 0 < scale)
    {bounds : NatInterval} {value : ℝ} (enclosed : bounds.Encloses scale value) : 0 ≤ value := by
  have scalePositive : (0 : ℝ) < scale := by exact_mod_cast positive
  have lowerPositive : (0 : ℝ) ≤ bounds.lower := by positivity
  unfold NatInterval.Encloses at enclosed
  nlinarith [enclosed.1]

theorem NatInterval.add_sound {scale : ℕ} {first second : NatInterval} {x y : ℝ}
    (firstEnclosed : first.Encloses scale x) (secondEnclosed : second.Encloses scale y) :
    (first.add second).Encloses scale (x+y) := by
  unfold NatInterval.Encloses NatInterval.add at *
  push_cast
  constructor <;> linarith [firstEnclosed.1,firstEnclosed.2,secondEnclosed.1,secondEnclosed.2]

theorem NatInterval.divide_sound {scale denominator : ℕ} (positive : 0 < denominator)
    {bounds : NatInterval} {value : ℝ} (enclosed : bounds.Encloses scale value) :
    (bounds.divide denominator).Encloses scale (value/denominator) := by
  have denominatorPositive : (0 : ℝ) < denominator := by exact_mod_cast positive
  have lower := (nat_division_outward bounds.lower denominator positive).1
  have upper := (nat_division_outward bounds.upper denominator positive).2
  unfold NatInterval.Encloses NatInterval.divide at *
  simp only [← mul_div_assoc]
  constructor
  · exact (le_div_iff₀ denominatorPositive).2 (lower.trans enclosed.1)
  · exact (div_le_iff₀ denominatorPositive).2 (enclosed.2.trans upper)

theorem NatInterval.mulThree_sound {scale : ℕ} (positive : 0 < scale)
    {first second third : NatInterval} {x y z : ℝ}
    (firstEnclosed : first.Encloses scale x) (secondEnclosed : second.Encloses scale y)
    (thirdEnclosed : third.Encloses scale z) :
    (NatInterval.mulThree scale first second third).Encloses scale (x*y*z) := by
  have xNonnegative := NatInterval.nonnegative positive firstEnclosed
  have yNonnegative := NatInterval.nonnegative positive secondEnclosed
  have zNonnegative := NatInterval.nonnegative positive thirdEnclosed
  have scalePositive : (0 : ℝ) < scale := by exact_mod_cast positive
  have squarePositive : (0 : ℝ) < (scale : ℝ)*(scale : ℝ) := mul_pos scalePositive scalePositive
  have lowerRound := (nat_division_outward (first.lower*second.lower*third.lower)
    (scale*scale) (Nat.mul_pos positive positive)).1
  have upperRound := (nat_division_outward (first.upper*second.upper*third.upper)
    (scale*scale) (Nat.mul_pos positive positive)).2
  have lowerTwo : (first.lower : ℝ)*second.lower ≤ ((scale : ℝ)*x)*((scale : ℝ)*y) :=
    mul_le_mul firstEnclosed.1 secondEnclosed.1 (by positivity) (by positivity)
  have lowerThree : ((first.lower : ℝ)*second.lower)*third.lower ≤
      (((scale : ℝ)*x)*((scale : ℝ)*y))*((scale : ℝ)*z) :=
    mul_le_mul lowerTwo thirdEnclosed.1 (by positivity) (by positivity)
  have upperTwo : ((scale : ℝ)*x)*((scale : ℝ)*y) ≤ (first.upper : ℝ)*second.upper :=
    mul_le_mul firstEnclosed.2 secondEnclosed.2 (by positivity) (by positivity)
  have upperThree : (((scale : ℝ)*x)*((scale : ℝ)*y))*((scale : ℝ)*z) ≤
      ((first.upper : ℝ)*second.upper)*third.upper :=
    mul_le_mul upperTwo thirdEnclosed.2 (by positivity) (by positivity)
  unfold NatInterval.Encloses NatInterval.mulThree
  dsimp only
  push_cast
  constructor
  · apply le_of_mul_le_mul_left (a := (scale : ℝ)*(scale : ℝ)) _ squarePositive
    push_cast at lowerRound
    nlinarith [lowerThree,lowerRound]
  · apply le_of_mul_le_mul_left (a := (scale : ℝ)*(scale : ℝ)) _ squarePositive
    push_cast at upperRound
    nlinarith [upperThree,upperRound]

end LambdaCantor.Integer
