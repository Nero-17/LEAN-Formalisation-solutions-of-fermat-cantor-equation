import LambdaCantor.Integer.FixedPoint
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp

namespace LambdaCantor.Integer

/-- At step n, the first interval encloses z^(2*n+1), and the second encloses
the n-term logarithm series. Every operation uses integer lattice endpoints. -/
def atanhLoop (scale : ℕ) (parameter : NatInterval) : ℕ → NatInterval × NatInterval
  | 0 => (parameter,⟨0,0⟩)
  | terms+1 =>
    let previous := atanhLoop scale parameter terms
    (NatInterval.mulThree scale previous.1 parameter parameter,
      previous.2.add ((previous.1.add previous.1).divide (2*terms+1)))

theorem atanhLoop_sound (scale : ℕ) (positive : 0 < scale) (parameter : NatInterval)
    (z : ℝ) (enclosed : parameter.Encloses scale z) (terms : ℕ) :
    (atanhLoop scale parameter terms).1.Encloses scale (z^(2*terms+1)) ∧
    (atanhLoop scale parameter terms).2.Encloses scale
      (2*∑ i ∈ Finset.range terms, z^(2*i+1)/((2*i+1 : ℕ) : ℝ)) := by
  induction terms with
  | zero =>
    constructor
    · simpa [atanhLoop] using enclosed
    · simp [atanhLoop,NatInterval.Encloses]
  | succ terms ih =>
    have nextPower := NatInterval.mulThree_sound positive ih.1 enclosed enclosed
    have term := NatInterval.divide_sound (by omega : 0 < 2*terms+1)
      (NatInterval.add_sound ih.1 ih.1)
    have nextSum := NatInterval.add_sound ih.2 term
    constructor
    · simpa only [atanhLoop,show 2*(terms+1)+1=(2*terms+1)+1+1 by omega,
        pow_add,pow_one,mul_assoc] using nextPower
    · have sumEquality :
        (2*∑ i ∈ Finset.range (terms+1),z^(2*i+1)/((2*i+1 : ℕ) : ℝ)) =
        (2*∑ i ∈ Finset.range terms,z^(2*i+1)/((2*i+1 : ℕ) : ℝ))+
          (z^(2*terms+1)+z^(2*terms+1))/((2*terms+1 : ℕ) : ℝ) := by
        rw [Finset.sum_range_succ]
        ring
      rw [sumEquality]
      exact nextSum

/-- A slightly looser geometric remainder uses 1-z instead of 1-z².
This makes the certified fixed-point denominator scale-upper, with no
subtraction of large squared values. It remains outward for 0<=z<1. -/
def atanhInterval (scale : ℕ) (parameter : NatInterval) (terms : ℕ) : NatInterval :=
  let result := atanhLoop scale parameter terms
  ⟨result.2.lower,result.2.upper+
    (2*result.1.upper*scale)/(scale-parameter.upper)+1⟩

theorem atanhInterval_sound (scale : ℕ) (positive : 0 < scale) (parameter : NatInterval)
    (strict : parameter.upper < scale) (z : ℝ) (enclosed : parameter.Encloses scale z)
    (terms : ℕ) :
    (atanhInterval scale parameter terms).Encloses scale
      (Real.log ((1+z)/(1-z))) := by
  have scalePositive : (0 : ℝ) < scale := by exact_mod_cast positive
  have parameterUpper : (parameter.upper : ℝ) < scale := by exact_mod_cast strict
  have zNonnegative := NatInterval.nonnegative positive enclosed
  have zLess : z < 1 := by nlinarith [enclosed.2]
  have denominatorPositive : 0 < 1-z^2 := by nlinarith
  obtain ⟨powerEnclosed,sumEnclosed⟩ := atanhLoop_sound scale positive parameter z enclosed terms
  have seriesLower := Real.sum_range_le_log_div zNonnegative zLess terms
  have seriesUpper := Real.log_div_le_sum_range_add zNonnegative zLess terms
  have lowerBound : (2*∑ i ∈ Finset.range terms,z^(2*i+1)/((2*i+1 : ℕ) : ℝ)) ≤
      Real.log ((1+z)/(1-z)) := by
    push_cast
    linarith [seriesLower]
  have upperBound : Real.log ((1+z)/(1-z)) ≤
      (2*∑ i ∈ Finset.range terms,z^(2*i+1)/((2*i+1 : ℕ) : ℝ))+
        2*z^(2*terms+1)/(1-z^2) := by
    push_cast
    simp only [mul_div_assoc]
    linarith [seriesUpper]
  have differencePositive : 0 < scale-parameter.upper := Nat.sub_pos_of_lt strict
  have differenceCast : ((scale-parameter.upper : ℕ) : ℝ) =
      (scale : ℝ)-parameter.upper := by rw [Nat.cast_sub strict.le]
  have remainderRound := (nat_division_outward
    (2*(atanhLoop scale parameter terms).1.upper*scale)
    (scale-parameter.upper) differencePositive).2
  rw [differenceCast] at remainderRound
  push_cast at remainderRound
  have denominatorLower : (scale : ℝ)-parameter.upper ≤ (scale : ℝ)*(1-z^2) := by
    have square : z^2 ≤ z := by nlinarith
    have scaled := mul_le_mul_of_nonneg_left square scalePositive.le
    nlinarith [enclosed.2]
  have multiplied := mul_le_mul_of_nonneg_left denominatorLower
    (show (0 : ℝ) ≤ ((2*(atanhLoop scale parameter terms).1.upper*scale /
      (scale-parameter.upper)+1 : ℕ) : ℝ) by positivity)
  push_cast at multiplied
  have remainderBound : (scale : ℝ)*(2*z^(2*terms+1)/(1-z^2)) ≤
      ((2*(atanhLoop scale parameter terms).1.upper*scale /
        (scale-parameter.upper)+1 : ℕ) : ℝ) := by
    simp only [← mul_div_assoc]
    apply (div_le_iff₀ denominatorPositive).2
    apply le_of_mul_le_mul_left (a := (scale : ℝ)) _ scalePositive
    have scaledPower := mul_le_mul_of_nonneg_left powerEnclosed.2 scalePositive.le
    push_cast
    nlinarith [multiplied,remainderRound,scaledPower]
  push_cast at remainderBound
  unfold NatInterval.Encloses at sumEnclosed ⊢
  unfold atanhInterval
  dsimp only
  constructor
  · exact sumEnclosed.1.trans (mul_le_mul_of_nonneg_left lowerBound scalePositive.le)
  · have scaledUpper := mul_le_mul_of_nonneg_left upperBound scalePositive.le
    push_cast
    nlinarith [sumEnclosed.2,remainderBound,scaledUpper]

/-- Outward parameter for log(numerator/denominator), with numerator >= denominator. -/
def logParameter (scale numerator denominator : ℕ) : NatInterval :=
  ⟨scale*(numerator-denominator)/(numerator+denominator),
    scale*(numerator-denominator)/(numerator+denominator)+1⟩

theorem logParameter_sound (scale numerator denominator : ℕ)
    (positive : 0 < denominator) (ordered : denominator ≤ numerator) :
    (logParameter scale numerator denominator).Encloses scale
      (((numerator : ℝ)-denominator)/(numerator+denominator)) := by
  have sumPositive : 0 < numerator+denominator := by omega
  have sumRealPositive : (0 : ℝ) < (numerator : ℝ)+denominator := by
    exact_mod_cast sumPositive
  have rounded := nat_division_outward (scale*(numerator-denominator))
    (numerator+denominator) sumPositive
  simp only [Nat.cast_mul,Nat.cast_sub ordered,Nat.cast_add] at rounded
  unfold NatInterval.Encloses logParameter
  dsimp only
  simp only [← mul_div_assoc,Nat.cast_add,Nat.cast_one] at rounded ⊢
  exact ⟨(le_div_iff₀ sumRealPositive).2 rounded.1,
    (div_le_iff₀ sumRealPositive).2 rounded.2⟩

def logUnitInterval (scale numerator denominator terms : ℕ) : NatInterval :=
  atanhInterval scale (logParameter scale numerator denominator) terms

theorem logUnitInterval_sound (scale numerator denominator terms : ℕ)
    (scalePositive : 0 < scale) (denominatorPositive : 0 < denominator)
    (ordered : denominator ≤ numerator)
    (strict : (logParameter scale numerator denominator).upper < scale) :
    (logUnitInterval scale numerator denominator terms).Encloses scale
      (Real.log ((numerator : ℝ)/denominator)) := by
  have denominatorRealPositive : (0 : ℝ) < denominator := by
    exact_mod_cast denominatorPositive
  have numeratorRealPositive : (0 : ℝ) < numerator := by
    exact_mod_cast (lt_of_lt_of_le denominatorPositive ordered)
  have sumNonzero : (numerator : ℝ)+denominator ≠ 0 := by positivity
  have oneMinusNonzero :
      1-((numerator : ℝ)-denominator)/(numerator+denominator) ≠ 0 := by
    apply ne_of_gt
    apply sub_pos.mpr
    apply (div_lt_one (by positivity : (0 : ℝ) < (numerator : ℝ)+denominator)).2
    linarith
  have identity :
      (1+((numerator : ℝ)-denominator)/(numerator+denominator))/
        (1-((numerator : ℝ)-denominator)/(numerator+denominator)) =
      (numerator : ℝ)/denominator := by
    field_simp [sumNonzero,oneMinusNonzero,ne_of_gt denominatorRealPositive]
    <;> ring
  have enclosed := atanhInterval_sound scale scalePositive
    (logParameter scale numerator denominator) strict _
    (logParameter_sound scale numerator denominator denominatorPositive ordered) terms
  rw [identity] at enclosed
  exact enclosed

end LambdaCantor.Integer
