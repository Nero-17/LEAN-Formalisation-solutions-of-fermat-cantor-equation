import LambdaCantor.Integer.TailPhaseIntervals

namespace LambdaCantor.Integer

def LogRatioChecked (scale numerator denominator : ℕ) : Prop :=
  0 < scale ∧ 0 < numerator ∧ 0 < denominator ∧
    signedLogStrict scale numerator denominator ∧ signedLogStrict scale 3 1 ∧
    0 < (signedLogInterval scale 3 1 80).lower ∧
    0 < (signedLogInterval scale 3 1 80).upper

instance (scale numerator denominator : ℕ) : Decidable (LogRatioChecked scale numerator denominator) := by
  unfold LogRatioChecked
  infer_instance

def logRatioLatticeInterval (scale multiple numerator denominator terms : ℕ) : IntInterval :=
  ((signedLogInterval scale numerator denominator terms).scaleBy multiple).divideBetween
    (signedLogInterval scale 3 1 80)

theorem logRatioLatticeInterval_sound (scale multiple numerator denominator terms : ℕ)
    (checked : LogRatioChecked scale numerator denominator) :
    (logRatioLatticeInterval scale multiple numerator denominator terms).Encloses 1
      ((multiple : ℝ)*Real.log ((numerator : ℝ)/denominator)/Real.log 3) := by
  obtain ⟨scalePositive,numeratorPositive,denominatorPositive,strict,strictThree,lower,upper⟩ := checked
  have numeratorEnclosed := IntInterval.scaleBy_sound (coefficient := multiple)
    (signedLogInterval_sound scale numerator denominator terms
      scalePositive numeratorPositive denominatorPositive strict)
  have denominatorEnclosed := signedLogInterval_sound scale 3 1 80 scalePositive
    (by decide) (by decide) strictThree
  simp only [Nat.cast_ofNat,Nat.cast_one,div_one] at denominatorEnclosed
  exact IntInterval.divideBetween_sound scale scalePositive _ _ lower upper _ _
    (Real.log_pos (by norm_num)) numeratorEnclosed denominatorEnclosed

def TailPhaseChecked (scale phaseScale minimum length a : ℕ) : Prop :=
  0 < phaseScale ∧ 0 < minimum ∧ 0 < length ∧
    LogRatioChecked scale (2*minimum*length+27*length) (2*minimum*length+2*a)

instance (scale phaseScale minimum length a : ℕ) :
    Decidable (TailPhaseChecked scale phaseScale minimum length a) := by
  unfold TailPhaseChecked
  infer_instance

theorem tailPhaseInterval_sound (scale phaseScale minimum length a : ℕ)
    (checked : TailPhaseChecked scale phaseScale minimum length a)
    (Z : ℝ) (large : (minimum : ℝ) ≤ Z) :
    (tailPhaseInterval scale phaseScale minimum length a).Encloses phaseScale
      (Z*Real.log ((Z+27/2)/(Z+(a : ℝ)/length))/Real.log 3) := by
  obtain ⟨phasePositive,minimumPositive,lengthPositive,logChecked⟩ := checked
  have lengthRealPositive : (0 : ℝ) < length := by exact_mod_cast lengthPositive
  have minimumRealPositive : (0 : ℝ) < minimum := by exact_mod_cast minimumPositive
  have ratioIdentity : ((2*minimum*length+27*length : ℕ) : ℝ)/(2*minimum*length+2*a : ℕ) =
      ((minimum : ℝ)+27/2)/(minimum+(a : ℝ)/length) := by
    push_cast
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    field_simp [ne_of_gt lengthRealPositive]
    <;> ring
  have finite := logRatioLatticeInterval_sound scale (phaseScale*minimum)
    (2*minimum*length+27*length) (2*minimum*length+2*a) 10 logChecked
  rw [ratioIdentity] at finite
  have finiteEnclosed : (tailPhaseFiniteInterval scale phaseScale minimum length a).Encloses phaseScale
      ((minimum : ℝ)*Real.log (((minimum : ℝ)+27/2)/(minimum+(a : ℝ)/length))/Real.log 3) := by
    simpa only [tailPhaseFiniteInterval,logRatioLatticeInterval,IntInterval.Encloses,
      Nat.cast_one,one_mul,Nat.cast_mul,mul_div_assoc,mul_assoc] using finite
  have limitingNumerator := rationalLatticeInterval_sound scale
    ((phaseScale : ℤ)*(27*(length : ℤ)-2*a)) (2*length) (by omega)
  have denominatorEnclosed := signedLogInterval_sound scale 3 1 80 logChecked.1
    (by decide) (by decide) logChecked.2.2.2.2.1
  simp only [Nat.cast_ofNat,Nat.cast_one,div_one] at denominatorEnclosed
  have limiting := IntInterval.divideBetween_sound scale logChecked.1 _ _
    logChecked.2.2.2.2.2.1 logChecked.2.2.2.2.2.2 _ _ (Real.log_pos (by norm_num))
    limitingNumerator denominatorEnclosed
  have numeratorIdentity : (((phaseScale : ℤ)*(27*(length : ℤ)-2*a) : ℤ) : ℝ)/(2*length : ℕ) =
      (phaseScale : ℝ)*(27/2-(a : ℝ)/length) := by
    push_cast
    field_simp [ne_of_gt lengthRealPositive]
    <;> ring
  have limitEnclosed : (tailPhaseLimitInterval scale phaseScale length a).Encloses phaseScale
      ((27/2-(a : ℝ)/length)/Real.log 3) := by
    simpa only [tailPhaseLimitInterval,IntInterval.Encloses,Nat.cast_one,one_mul,
      numeratorIdentity,mul_div_assoc] using limiting
  exact tailPhaseInterval_union_sound phaseScale phasePositive minimum Z ((a : ℝ)/length) (27/2)
    (by exact_mod_cast minimumPositive) large (by positivity) (by norm_num)
    _ _ finiteEnclosed limitEnclosed

end LambdaCantor.Integer
