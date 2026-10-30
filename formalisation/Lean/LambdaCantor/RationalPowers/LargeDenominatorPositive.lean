import LambdaCantor.RationalPowers.LogSourcePhase
import LambdaCantor.RationalPowers.LogSourcePositiveDimension
import LambdaCantor.RationalPowers.ReciprocalLogSourcePositiveDimension
import LambdaCantor.Integer.PrefixConcatenation
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FinCases

noncomputable section
namespace LambdaCantor.RationalPowers
open Integer

/-- Every row in the sixteen-source cover lies in a proved direct band or
in the reciprocal of a proved band. This theorem checks the actual decoder. -/
theorem denominatorSource_orientations (index : Fin 16) :
    (1 < ((denominatorSources index).lowerSlope : ℝ) ∧
      ((denominatorSources index).upperSlope : ℝ) < 3 ∧
      ∀ slope : ℝ, ((denominatorSources index).lowerSlope : ℝ) < slope →
        slope < ((denominatorSources index).upperSlope : ℝ) → GoodSlope slope) ∨
    (1/3 < ((denominatorSources index).lowerSlope : ℝ) ∧
      ((denominatorSources index).upperSlope : ℝ) < 1 ∧
      ∀ slope : ℝ, 1/((denominatorSources index).upperSlope : ℝ) < slope →
        slope < 1/((denominatorSources index).lowerSlope : ℝ) → GoodSlope slope) := by
  fin_cases index
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inr ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inr ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inr (Or.inr (Or.inl ⟨lower,upper⟩))
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨lower,upper⟩)))
  · refine Or.inl ⟨by norm_num [denominatorSources], by norm_num [denominatorSources], ?_⟩
    intro slope lower upper
    norm_num [denominatorSources] at lower upper
    exact Or.inl ⟨lower,upper⟩

/-- The exact sixteen-row source cover yields actual positive Hausdorff
dimension for every reduced rational exponent with denominator at least 110.
All exponent scales are realized by appending legal horizontal zero digits. -/
theorem large_denominator_rational_positive_dimension (numerator denominator : ℕ)
    (coprime : numerator.Coprime denominator) (denominator_cutoff : 110 ≤ denominator)
    (exponent_gt_one : 1 < (numerator : ℝ)/denominator) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) := by
  have denominator_positive : 0 < denominator := by omega
  have denominator_real_positive : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  have exponent_ne_two : (numerator : ℝ)/denominator ≠ 2 := by
    intro equality
    have numerator_eq : numerator = 2*denominator := by
      exact_mod_cast (div_eq_iff denominator_real_positive.ne').mp equality
    have gcd := coprime.gcd_eq_one
    rw [numerator_eq, Nat.gcd_mul_left_left] at gcd
    omega
  obtain ⟨shift, power_lower, power_upper⟩ :=
    exists_nat_pow_near exponent_gt_one.le (by norm_num : (1 : ℝ) < 3)
  have power_positive : 0 < (3 : ℝ)^shift := by positivity
  have normalized_lower : 1 ≤ ((numerator : ℝ)/denominator)/(3 : ℝ)^shift :=
    (le_div_iff₀ power_positive).mpr (by simpa using power_lower)
  have normalized_upper : ((numerator : ℝ)/denominator)/(3 : ℝ)^shift ≤ 3 := by
    apply (div_le_iff₀ power_positive).mpr
    rw [pow_succ] at power_upper
    nlinarith
  obtain ⟨index, phase, checked, lower, upper, lower_corner, upper_corner⟩ :=
    large_denominator_log_source (((numerator : ℝ)/denominator)/(3 : ℝ)^shift) ((3 : ℝ)^shift)
      normalized_lower normalized_upper (one_le_pow₀ (by norm_num)) (6+shift) 6 denominator denominator_cutoff
  have exponent_identity : (3 : ℝ)^shift*(((numerator : ℝ)/denominator)/(3 : ℝ)^shift) =
      (numerator : ℝ)/denominator := by field_simp
  rw [exponent_identity] at lower upper lower_corner upper_corner
  have horizontal_identity : (((denominatorSources index).horizontal*3^shift : ℕ) : ℝ) =
      (3 : ℝ)^shift*(denominatorSources index).horizontal := by push_cast; ring
  rw [← horizontal_identity] at lower upper lower_corner upper_corner
  have horizontal_positive : 0 < (denominatorSources index).horizontal*3^shift :=
    Nat.mul_pos checked.1 (by positivity)
  have horizontal_real_positive : (0 : ℝ) < (((denominatorSources index).horizontal*3^shift : ℕ) : ℝ) := by
    exact_mod_cast horizontal_positive
  have vertical_real_positive : (0 : ℝ) < (denominatorSources index).vertical := by
    exact_mod_cast checked.2.1
  have horizontal_prefix := ternaryPrefix_append (denominatorSources index).horizontal 0 6 shift
    checked.2.2.1 (ternaryPrefix_zero shift)
  simp only [Nat.add_zero] at horizontal_prefix
  have lower_ratio : ((denominatorSources index).lowerSlope : ℝ)/(denominatorSources index).vertical <
      ((numerator : ℝ)/denominator)/(((denominatorSources index).horizontal*3^shift : ℕ)+1) := by
    apply (div_lt_div_iff₀ vertical_real_positive (by positivity)).mpr
    have cleared := (lt_div_iff₀ (by positivity : (0 : ℝ) <
      (((denominatorSources index).horizontal*3^shift : ℕ) : ℝ)+1)).mp lower
    nlinarith
  have upper_ratio : ((numerator : ℝ)/denominator)/((denominatorSources index).horizontal*3^shift : ℕ) <
      ((denominatorSources index).upperSlope : ℝ)/((denominatorSources index).vertical+1) := by
    apply (div_lt_div_iff₀ horizontal_real_positive (by positivity)).mpr
    have cleared := (div_lt_iff₀ horizontal_real_positive).mp upper
    nlinarith
  have upper_positive : 0 < ((denominatorSources index).upperSlope : ℝ) := by
    have rational_positive := checked.2.2.2.2.2.2.1.trans checked.2.2.2.2.2.2.2.1
    exact_mod_cast rational_positive
  rcases denominatorSource_orientations index with direct | reciprocal
  · exact strict_rational_log_source_positive_dimension numerator denominator phase
      denominator_positive coprime exponent_gt_one exponent_ne_two
      (6+shift) 6 ((denominatorSources index).horizontal*3^shift) (denominatorSources index).vertical
      (denominatorSources index).lowerSlope (denominatorSources index).upperSlope
      horizontal_positive checked.2.1 horizontal_prefix checked.2.2.2.1 checked.2.2.2.2.2.1
      direct.1 direct.2.1 upper_positive direct.2.2 lower_ratio upper_ratio lower_corner upper_corner
  · exact reciprocal_strict_rational_log_source_positive_dimension numerator denominator phase
      denominator_positive coprime exponent_gt_one exponent_ne_two
      (6+shift) 6 ((denominatorSources index).horizontal*3^shift) (denominatorSources index).vertical
      (denominatorSources index).lowerSlope (denominatorSources index).upperSlope
      horizontal_positive checked.2.1 horizontal_prefix checked.2.2.2.1 checked.2.2.2.2.2.1
      reciprocal.1 reciprocal.2.1 upper_positive reciprocal.2.2 lower_ratio upper_ratio lower_corner upper_corner

end LambdaCantor.RationalPowers
