import LambdaCantor.Integer.FixedSignedArithmetic
import LambdaCantor.Integer.TailPhaseBounds

namespace LambdaCantor.Integer

def tailPhaseFiniteInterval (scale phaseScale minimum length a : ℕ) : IntInterval :=
  ((signedLogInterval scale (2*minimum*length+27*length)
    (2*minimum*length+2*a) 10).scaleBy (phaseScale*minimum)).divideBetween
      (signedLogInterval scale 3 1 80)

def tailPhaseLimitInterval (scale phaseScale length a : ℕ) : IntInterval :=
  (rationalLatticeInterval scale ((phaseScale : ℤ)*(27*(length : ℤ)-2*a))
    (2*length)).divideBetween (signedLogInterval scale 3 1 80)

def tailPhaseInterval (scale phaseScale minimum length a : ℕ) : IntInterval :=
  let finite := tailPhaseFiniteInterval scale phaseScale minimum length a
  let limiting := tailPhaseLimitInterval scale phaseScale length a
  ⟨min finite.lower limiting.lower,max finite.upper limiting.upper⟩

/-- The generic union-of-endpoints step used after the finite logarithmic and
limiting rational intervals have individually been verified. -/
theorem tailPhaseInterval_union_sound (phaseScale : ℕ) (phaseScalePositive : 0 < phaseScale)
    (minimum Z a b : ℝ) (minimumPositive : 0 < minimum) (large : minimum ≤ Z)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (finite limiting : IntInterval)
    (finiteEnclosed : finite.Encloses phaseScale
      (minimum*Real.log ((minimum+b)/(minimum+a))/Real.log 3))
    (limitEnclosed : limiting.Encloses phaseScale ((b-a)/Real.log 3)) :
    (IntInterval.mk (min finite.lower limiting.lower) (max finite.upper limiting.upper)).Encloses
      phaseScale (Z*Real.log ((Z+b)/(Z+a))/Real.log 3) := by
  have scalePositive : (0 : ℝ) < phaseScale := by exact_mod_cast phaseScalePositive
  have lowerFinite : ((min finite.lower limiting.lower : ℤ) : ℝ) ≤ finite.lower := by
    exact_mod_cast (min_le_left finite.lower limiting.lower)
  have lowerLimit : ((min finite.lower limiting.lower : ℤ) : ℝ) ≤ limiting.lower := by
    exact_mod_cast (min_le_right finite.lower limiting.lower)
  have upperFinite : (finite.upper : ℝ) ≤ max finite.upper limiting.upper := by
    exact_mod_cast (le_max_left finite.upper limiting.upper)
  have upperLimit : (limiting.upper : ℝ) ≤ max finite.upper limiting.upper := by
    exact_mod_cast (le_max_right finite.upper limiting.upper)
  have result := tail_phase_enclosure minimum Z a b
    (((min finite.lower limiting.lower : ℤ) : ℝ)/phaseScale)
    (((max finite.upper limiting.upper : ℤ) : ℝ)/phaseScale)
    minimumPositive large aNonnegative bNonnegative
    ((div_le_iff₀ scalePositive).2 (by nlinarith [finiteEnclosed.1]))
    ((le_div_iff₀ scalePositive).2 (by nlinarith [finiteEnclosed.2]))
    ((div_le_iff₀ scalePositive).2 (by nlinarith [limitEnclosed.1]))
    ((le_div_iff₀ scalePositive).2 (by nlinarith [limitEnclosed.2]))
  unfold IntInterval.Encloses
  dsimp only
  constructor
  · have bound := (div_le_iff₀ scalePositive).1 result.1
    nlinarith
  · have bound := (le_div_iff₀ scalePositive).1 result.2
    nlinarith

end LambdaCantor.Integer
