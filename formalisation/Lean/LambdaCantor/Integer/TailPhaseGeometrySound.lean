import LambdaCantor.Integer.TailPhaseSourceSound
import LambdaCantor.Integer.GoodSlopes
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace LambdaCantor.Integer

theorem tailPhaseBand_denominators (band : Fin 4) :
    0 < (tailPhaseBand band).2.1 ∧ 0 < (tailPhaseBand band).2.2.2 := by
  fin_cases band <;> decide

theorem TailPhaseGeometry.Checked.real_ratios (geometry : TailPhaseGeometry) (cell : ℕ)
    (band : Fin 4) (checked : geometry.Checked cell band)
    (Z coefficient : ℝ) (large : 1180980 ≤ Z)
    (coefficientLower : 2*(cell : ℝ)-1 ≤ 4000*coefficient)
    (coefficientUpper : 4000*coefficient ≤ 2*(cell : ℝ)+1) :
    ((tailPhaseBand band).1 : ℝ)/(tailPhaseBand band).2.1 <
      coefficient*geometry.q*Z/(Z*tailPhaseLength geometry+geometry.a+1) ∧
    coefficient*(geometry.q+1)*Z/(Z*tailPhaseLength geometry+geometry.a) <
      ((tailPhaseBand band).2.2.1 : ℝ)/(tailPhaseBand band).2.2.2 := by
  obtain ⟨_,_,_,_,_,_,_,cellPositive,lower,upper⟩ := checked
  have cellRealPositive : (1 : ℝ) ≤ cell := by exact_mod_cast cellPositive
  have lengthPositive : (0 : ℝ) < tailPhaseLength geometry := by
    unfold tailPhaseLength
    positivity
  have denominators := tailPhaseBand_denominators band
  have lowerDenominator : (0 : ℝ) < (tailPhaseBand band).2.1 := by exact_mod_cast denominators.1
  have upperDenominator : (0 : ℝ) < (tailPhaseBand band).2.2.2 := by exact_mod_cast denominators.2
  have lowerReal : ((tailPhaseBand band).1 : ℝ)*4000*
      (1180980*(tailPhaseLength geometry : ℝ)+geometry.a+1) <
      (tailPhaseBand band).2.1*(2*(cell : ℝ)-1)*geometry.q*1180980 := by
    have castLower : ((tailPhaseBand band).1 : ℝ)*4000*
        (1180980*(tailPhaseLength geometry : ℝ)+geometry.a+1) <
        (tailPhaseBand band).2.1*((2*cell-1 : ℕ) : ℝ)*geometry.q*1180980 := by
      exact_mod_cast lower
    simpa only [Nat.cast_sub (show 1 ≤ 2*cell by omega),Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      using castLower
  have upperReal : ((tailPhaseBand band).2.2.2 : ℝ)*(2*(cell : ℝ)+1)*(geometry.q+1) <
      (tailPhaseBand band).2.2.1*4000*(tailPhaseLength geometry : ℝ) := by
    exact_mod_cast upper
  have derivative := tail_derivative_bounds 1180980 Z (tailPhaseLength geometry) geometry.a
    coefficient ((2*(cell : ℝ)-1)/4000) ((2*(cell : ℝ)+1)/4000) geometry.q
    (by norm_num) large lengthPositive (by positivity) (by positivity)
    (by apply div_nonneg _ (by norm_num); linarith)
    ((div_le_iff₀ (by norm_num : (0 : ℝ) < 4000)).2 (by simpa only [mul_comm] using coefficientLower))
    ((le_div_iff₀ (by norm_num : (0 : ℝ) < 4000)).2 (by simpa only [mul_comm] using coefficientUpper))
  constructor
  · apply lt_of_lt_of_le _ derivative.1
    apply (div_lt_div_iff₀ lowerDenominator (by positivity)).2
    nlinarith [lowerReal]
  · apply lt_of_le_of_lt derivative.2
    apply (div_lt_div_iff₀ lengthPositive upperDenominator).2
    nlinarith [upperReal]

theorem tailPhaseBand_good (band : Fin 4) (slope : ℝ)
    (lower : ((tailPhaseBand band).1 : ℝ)/(tailPhaseBand band).2.1 < slope)
    (upper : slope < ((tailPhaseBand band).2.2.1 : ℝ)/(tailPhaseBand band).2.2.2) :
    GoodSlope slope ∨ GoodSlope (1/slope) := by
  fin_cases band <;> norm_num [tailPhaseBand] at lower upper
  · left
    apply Or.inl
    constructor <;> linarith
  · left
    refine Or.inr (Or.inr (Or.inl ?_))
    constructor <;> linarith
  · right
    apply Or.inl
    have positive : 0 < slope := by linarith
    constructor
    · apply (lt_div_iff₀ positive).2
      linarith
    · apply (div_lt_iff₀ positive).2
      linarith
  · right
    refine Or.inr (Or.inr (Or.inl ?_))
    have positive : 0 < slope := by linarith
    constructor
    · apply (lt_div_iff₀ positive).2
      linarith
    · apply (div_lt_iff₀ positive).2
      linarith

end LambdaCantor.Integer
