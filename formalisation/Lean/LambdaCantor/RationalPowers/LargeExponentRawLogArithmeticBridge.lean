import LambdaCantor.RationalPowers.LargeExponentRawLogCore
import LambdaCantor.RationalPowers.LargeExponentRawPhaseBridge

namespace LambdaCantor.RationalPowers

/-- Preserve the two natural-number endpoints without changing their lattice. -/
def RawLog.NatInterval.toNatInterval (bounds : RawLog.NatInterval) : Integer.NatInterval :=
  ⟨bounds.lower,bounds.upper⟩

theorem largeExponent_raw_log_nat_add_eq (first second : RawLog.NatInterval) :
    (first.add second).toNatInterval = first.toNatInterval.add second.toNatInterval := by
  rfl

theorem largeExponent_raw_log_nat_divide_eq (bounds : RawLog.NatInterval) (denominator : Nat) :
    (bounds.divide denominator).toNatInterval = bounds.toNatInterval.divide denominator := by
  rfl

theorem largeExponent_raw_log_nat_mul_three_eq (scale : Nat)
    (first second third : RawLog.NatInterval) :
    (RawLog.NatInterval.mulThree scale first second third).toNatInterval =
      Integer.NatInterval.mulThree scale first.toNatInterval second.toNatInterval
        third.toNatInterval := by
  rfl

theorem largeExponent_raw_log_atanh_loop_eq (scale : Nat)
    (parameter : RawLog.NatInterval) (terms : Nat) :
    ((RawLog.atanhLoop scale parameter terms).1.toNatInterval,
      (RawLog.atanhLoop scale parameter terms).2.toNatInterval) =
      Integer.atanhLoop scale parameter.toNatInterval terms := by
  induction terms with
  | zero => rfl
  | succ terms induction_hypothesis =>
    have power_identity := congrArg Prod.fst induction_hypothesis
    have sum_identity := congrArg Prod.snd induction_hypothesis
    simp only [Prod.fst,Prod.snd] at power_identity sum_identity
    simp only [RawLog.atanhLoop,Integer.atanhLoop,
      largeExponent_raw_log_nat_mul_three_eq,largeExponent_raw_log_nat_add_eq,
      largeExponent_raw_log_nat_divide_eq,power_identity,sum_identity]

theorem largeExponent_raw_log_atanh_loop_fst_eq (scale : Nat)
    (parameter : RawLog.NatInterval) (terms : Nat) :
    (RawLog.atanhLoop scale parameter terms).1.toNatInterval =
      (Integer.atanhLoop scale parameter.toNatInterval terms).1 := by
  exact congrArg Prod.fst (largeExponent_raw_log_atanh_loop_eq scale parameter terms)

theorem largeExponent_raw_log_atanh_loop_snd_eq (scale : Nat)
    (parameter : RawLog.NatInterval) (terms : Nat) :
    (RawLog.atanhLoop scale parameter terms).2.toNatInterval =
      (Integer.atanhLoop scale parameter.toNatInterval terms).2 := by
  exact congrArg Prod.snd (largeExponent_raw_log_atanh_loop_eq scale parameter terms)

theorem largeExponent_raw_log_atanh_interval_eq (scale : Nat)
    (parameter : RawLog.NatInterval) (terms : Nat) :
    (RawLog.atanhInterval scale parameter terms).toNatInterval =
      Integer.atanhInterval scale parameter.toNatInterval terms := by
  have power_upper : (RawLog.atanhLoop scale parameter terms).1.upper =
      (Integer.atanhLoop scale parameter.toNatInterval terms).1.upper :=
    congrArg Integer.NatInterval.upper
      (largeExponent_raw_log_atanh_loop_fst_eq scale parameter terms)
  have sum_lower : (RawLog.atanhLoop scale parameter terms).2.lower =
      (Integer.atanhLoop scale parameter.toNatInterval terms).2.lower :=
    congrArg Integer.NatInterval.lower
      (largeExponent_raw_log_atanh_loop_snd_eq scale parameter terms)
  have sum_upper : (RawLog.atanhLoop scale parameter terms).2.upper =
      (Integer.atanhLoop scale parameter.toNatInterval terms).2.upper :=
    congrArg Integer.NatInterval.upper
      (largeExponent_raw_log_atanh_loop_snd_eq scale parameter terms)
  simp only [RawLog.atanhInterval,Integer.atanhInterval,RawLog.NatInterval.toNatInterval,
    power_upper,sum_lower,sum_upper]

theorem largeExponent_raw_log_parameter_eq (scale numerator denominator : Nat) :
    (RawLog.logParameter scale numerator denominator).toNatInterval =
      Integer.logParameter scale numerator denominator := by
  rfl

theorem largeExponent_raw_log_unit_interval_eq (scale numerator denominator terms : Nat) :
    (RawLog.logUnitInterval scale numerator denominator terms).toNatInterval =
      Integer.logUnitInterval scale numerator denominator terms := by
  unfold RawLog.logUnitInterval Integer.logUnitInterval
  rw [largeExponent_raw_log_atanh_interval_eq,largeExponent_raw_log_parameter_eq]

theorem largeExponent_raw_log_signed_interval_eq (scale numerator denominator terms : Nat) :
    (RawLog.signedLogInterval scale numerator denominator terms).toInterval =
      Integer.signedLogInterval scale numerator denominator terms := by
  by_cases ordered : denominator ≤ numerator
  · simpa only [RawLog.signedLogInterval,Integer.signedLogInterval,if_pos ordered,
      RawPhase.Interval.toInterval,RawLog.NatInterval.toNatInterval] using
      congrArg (fun result : Integer.NatInterval =>
        (⟨(result.lower : Int),(result.upper : Int)⟩ : Integer.IntInterval))
        (largeExponent_raw_log_unit_interval_eq scale numerator denominator terms)
  · simpa only [RawLog.signedLogInterval,Integer.signedLogInterval,if_neg ordered,
      RawPhase.Interval.toInterval,RawLog.NatInterval.toNatInterval] using
      congrArg (fun result : Integer.NatInterval =>
        (⟨-(result.upper : Int),-(result.lower : Int)⟩ : Integer.IntInterval))
        (largeExponent_raw_log_unit_interval_eq scale denominator numerator terms)

theorem largeExponent_raw_log_signed_strict_eq (scale numerator denominator : Nat) :
    RawLog.signedLogStrict scale numerator denominator =
      Integer.signedLogStrict scale numerator denominator := by
  by_cases ordered : denominator ≤ numerator
  · simpa only [RawLog.signedLogStrict,Integer.signedLogStrict,if_pos ordered,
      RawLog.NatInterval.toNatInterval] using
      congrArg (fun result : Integer.NatInterval => result.upper < scale)
        (largeExponent_raw_log_parameter_eq scale numerator denominator)
  · simpa only [RawLog.signedLogStrict,Integer.signedLogStrict,if_neg ordered,
      RawLog.NatInterval.toNatInterval] using
      congrArg (fun result : Integer.NatInterval => result.upper < scale)
        (largeExponent_raw_log_parameter_eq scale denominator numerator)

theorem largeExponent_raw_log_scale_by_eq (bounds : RawPhase.Interval) (coefficient : Nat) :
    (RawLog.scaleBy bounds coefficient).toInterval = bounds.toInterval.scaleBy coefficient := by
  rfl

theorem largeExponent_raw_log_divide_between_eq (numerator denominator : RawPhase.Interval) :
    (RawLog.divideBetween numerator denominator).toInterval =
      numerator.toInterval.divideBetween denominator.toInterval := by
  rfl

/-- Exact endpoint identity, including all zero and invalid input cases. -/
theorem largeExponent_raw_log_ratio_interval_eq
    (scale multiple numerator denominator terms : Nat) :
    (RawLog.logRatioLatticeInterval scale multiple numerator denominator terms).toInterval =
      Integer.logRatioLatticeInterval scale multiple numerator denominator terms := by
  unfold RawLog.logRatioLatticeInterval Integer.logRatioLatticeInterval
  rw [largeExponent_raw_log_divide_between_eq,largeExponent_raw_log_scale_by_eq,
    largeExponent_raw_log_signed_interval_eq,largeExponent_raw_log_signed_interval_eq]

/-- The analytic input predicate is preserved exactly, without positivity assumptions. -/
theorem largeExponent_raw_log_ratio_checked_eq (scale numerator denominator : Nat) :
    RawLog.LogRatioChecked scale numerator denominator =
      Integer.LogRatioChecked scale numerator denominator := by
  have lower_identity : (RawLog.signedLogInterval scale 3 1 80).lower =
      (Integer.signedLogInterval scale 3 1 80).lower :=
    congrArg Integer.IntInterval.lower
      (largeExponent_raw_log_signed_interval_eq scale 3 1 80)
  have upper_identity : (RawLog.signedLogInterval scale 3 1 80).upper =
      (Integer.signedLogInterval scale 3 1 80).upper :=
    congrArg Integer.IntInterval.upper
      (largeExponent_raw_log_signed_interval_eq scale 3 1 80)
  simp only [RawLog.LogRatioChecked,Integer.LogRatioChecked,
    largeExponent_raw_log_signed_strict_eq,lower_identity,upper_identity]

end LambdaCantor.RationalPowers
