import LambdaCantor.First.RootsMeasures
import LambdaCantor.First.RootsIncidence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- The incidence mass exponent exceeds one throughout the supercritical band. -/
theorem incidence_exponent_gt_one {lower : ℝ} (quarter_lt : 1 / 4 < lower)
    (lower_lt_one : lower < 1) : 1 < Real.log 4 / Real.log (1 / lower) := by
  have lower_pos : 0 < lower := by linarith
  have reciprocal_gt_one : 1 < 1 / lower := (one_lt_div lower_pos).2 lower_lt_one
  have denominator_pos : 0 < Real.log (1 / lower) := Real.log_pos reciprocal_gt_one
  apply (one_lt_div denominator_pos).2
  apply Real.log_lt_log (by positivity)
  apply (div_lt_iff₀ lower_pos).2
  linarith

/-- The cylinder mass is the separation scale raised to the incidence exponent. -/
theorem incidence_exponent_identity {lower : ℝ} (lower_pos : 0 < lower)
    (lower_lt_one : lower < 1) :
    lower ^ (Real.log 4 / Real.log (1 / lower)) = (1 / 4 : ℝ) := by
  have log_ne : Real.log lower ≠ 0 := (Real.log_neg lower_pos lower_lt_one).ne
  have exponent_identity : Real.log lower *
      (Real.log 4 / Real.log (1 / lower)) = -Real.log 4 := by
    rw [Real.log_div one_ne_zero lower_pos.ne', Real.log_one, zero_sub]
    field_simp [log_ne] <;> ring
  rw [Real.rpow_def_of_pos lower_pos, exponent_identity, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-- Conversion from geometric-scale mass bounds to all sufficiently small radii.
The right side is a fixed constant times radius to the given exponent. -/
theorem interpolate_geometric_mass (mass : ℝ → ℝ) (monotone : Monotone mass)
    {scale contraction exponent radius : ℝ}
    (scale_pos : 0 < scale) (contraction_pos : 0 < contraction)
    (contraction_lt_one : contraction < 1) (exponent_pos : 0 < exponent)
    (radius_pos : 0 < radius) (radius_le : radius ≤ scale)
    (discrete_bound : ∀ depth : ℕ,
      mass (scale * contraction ^ depth) ≤ (contraction ^ exponent) ^ depth) :
    mass radius ≤ (radius / (scale * contraction)) ^ exponent := by
  obtain ⟨depth, lower_bound, upper_bound⟩ := exists_nat_pow_near_of_lt_one
    (div_pos radius_pos scale_pos) ((div_le_iff₀ scale_pos).2 (by simpa using radius_le))
    contraction_pos contraction_lt_one
  have radius_upper : radius ≤ scale * contraction ^ depth := by
    have := (div_le_iff₀ scale_pos).mp upper_bound
    simpa [mul_comm] using this
  have contraction_upper : contraction ^ depth < radius / (scale * contraction) := by
    apply (lt_div_iff₀ (mul_pos scale_pos contraction_pos)).2
    have := (lt_div_iff₀ scale_pos).mp lower_bound
    rw [pow_succ] at this
    nlinarith
  calc
    mass radius ≤ mass (scale * contraction ^ depth) := monotone radius_upper
    _ ≤ (contraction ^ exponent) ^ depth := discrete_bound depth
    _ = (contraction ^ depth) ^ exponent := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul contraction_pos.le,
        ← Real.rpow_natCast contraction, ← Real.rpow_mul contraction_pos.le]
      congr 1
      ring
    _ ≤ (radius / (scale * contraction)) ^ exponent :=
      (Real.rpow_lt_rpow (pow_nonneg contraction_pos.le _) contraction_upper exponent_pos).le

def incidencePoint (root : (ℕ → Bool × Bool) → ℝ) (digits : ℕ → Bool × Bool) :
    ℝ × ℝ × ℝ :=
  (root digits, address (root digits) (fun j => (digits j).1),
    address (root digits) (fun j => (digits j).2))

def incidenceSeparationRadius (lower upper : ℝ) (depth : ℕ) : ℝ :=
  (1 - 2 * upper) * lower ^ depth / (1 + |addressParameterDerivativeBound upper|)

/-- Incidence coordinates for fixed actual cylinders and unrestricted tails. -/
def cylinderIncidencePoint (root : (ℕ → Bool × Bool) → ℝ)
    (horizontalPrefix verticalPrefix : ℕ → Bool) (horizontalLength verticalLength : ℕ)
    (digits : ℕ → Bool × Bool) : ℝ × ℝ × ℝ :=
  (root digits,
    address (root digits) (cylinderDigits horizontalPrefix horizontalLength (fun j => (digits j).1)),
    address (root digits) (cylinderDigits verticalPrefix verticalLength (fun j => (digits j).2)))

/-- Joint address continuity turns the continuous root map into a continuous
actual-cylinder incidence map, hence into a measurable probability pushforward. -/
theorem continuous_cylinderIncidencePoint {lower upper : ℝ}
    (lower_nonnegative : 0 ≤ lower) (upper_lt_one : upper < 1) (ordered : lower ≤ upper)
    (root : (ℕ → Bool × Bool) → ℝ) (root_continuous : Continuous root)
    (root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper)
    (horizontalPrefix verticalPrefix : ℕ → Bool) (horizontalLength verticalLength : ℕ) :
    Continuous (cylinderIncidencePoint root horizontalPrefix verticalPrefix
      horizontalLength verticalLength) := by
  have root_band_continuous : Continuous
      (fun digits => (⟨root digits, root_in_band digits⟩ : Set.Icc lower upper)) :=
    root_continuous.subtype_mk _
  have left_continuous : Continuous (fun digits : ℕ → Bool × Bool =>
      fun index => (digits index).1) := by
    apply continuous_pi
    intro index
    exact continuous_fst.comp (continuous_apply index)
  have right_continuous : Continuous (fun digits : ℕ → Bool × Bool =>
      fun index => (digits index).2) := by
    apply continuous_pi
    intro index
    exact continuous_snd.comp (continuous_apply index)
  have address_continuous := continuous_address_band lower_nonnegative upper_lt_one ordered
  exact root_continuous.prodMk
    ((address_continuous.comp (root_band_continuous.prodMk
      ((continuous_cylinderDigits horizontalPrefix horizontalLength).comp left_continuous))).prodMk
      (address_continuous.comp (root_band_continuous.prodMk
        ((continuous_cylinderDigits verticalPrefix verticalLength).comp right_continuous))))

private theorem weighted_sum_lt {first second radius constant : ℝ}
    (first_lt : first < radius) (second_lt : second < radius)
    (second_nonnegative : 0 ≤ second) :
    first + constant * second < (1 + |constant|) * radius := by
  calc
    first + constant * second ≤ first + |constant| * second := by
      simpa only [add_comm] using!
        add_le_add_left (mul_le_mul_of_nonneg_right (le_abs_self constant) second_nonnegative) first
    _ < radius + |constant| * radius := add_lt_add_of_lt_of_le first_lt
      (mul_le_mul_of_nonneg_left second_lt.le (abs_nonneg _))
    _ = _ := by ring

/-- Incidence neighbourhood mass at a paired-cylinder scale. The underlying
measure is the actual fair product measure, and the root map is allowed to depend
on both complete addresses. No independence survives projection and none is assumed. -/
theorem incidence_neighbourhood_mass
    {lower upper : ℝ} (lower_pos : 0 < lower) (upper_lt : upper < 1 / 2)
    (root : (ℕ → Bool × Bool) → ℝ)
    (root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper)
    (digits : ℕ → Bool × Bool) (depth : ℕ) :
    pairedAddressMeasure {other |
      (|address (root digits) (fun j => (digits j).1) -
          address (root other) (fun j => (other j).1)| +
        addressParameterDerivativeBound upper * |root digits - root other| <
          (1 - 2 * upper) * lower ^ depth) ∧
      (|address (root digits) (fun j => (digits j).2) -
          address (root other) (fun j => (other j).2)| +
        addressParameterDerivativeBound upper * |root digits - root other| <
          (1 - 2 * upper) * lower ^ depth)} ≤ (1 / 4 : ℝ≥0∞) ^ depth := by
  rw [← pairedPrefix_mass digits depth]
  apply measure_mono
  intro other close
  have first := close_incidence_same_prefix lower_pos upper_lt (root_in_band digits)
    (root_in_band other) (fun j => (digits j).1) (fun j => (other j).1) depth close.1
  have second := close_incidence_same_prefix lower_pos upper_lt (root_in_band digits)
    (root_in_band other) (fun j => (digits j).2) (fun j => (other j).2) depth close.2
  intro j before
  exact Prod.ext (first j before).symm (second j before).symm

/-- Genuine metric-ball form of the incidence prefix-mass bound. The metric on
the three real coordinates is the standard product maximum metric. -/
theorem incidence_ball_mass {lower upper : ℝ} (lower_pos : 0 < lower)
    (upper_lt : upper < 1 / 2) (root : (ℕ → Bool × Bool) → ℝ)
    (root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper)
    (digits : ℕ → Bool × Bool) (depth : ℕ) :
    pairedAddressMeasure ((incidencePoint root) ⁻¹'
      Metric.ball (incidencePoint root digits) (incidenceSeparationRadius lower upper depth)) ≤
        (1 / 4 : ℝ≥0∞) ^ depth := by
  apply le_trans (measure_mono ?_) (incidence_neighbourhood_mass lower_pos upper_lt
    root root_in_band digits depth)
  intro other close
  change dist (incidencePoint root other) (incidencePoint root digits) <
    incidenceSeparationRadius lower upper depth at close
  simp only [incidencePoint, Prod.dist_eq, Real.dist_eq, max_lt_iff] at close
  have scale_identity : (1 + |addressParameterDerivativeBound upper|) *
      incidenceSeparationRadius lower upper depth = (1 - 2 * upper) * lower ^ depth := by
    have denominator_ne : 1 + |addressParameterDerivativeBound upper| ≠ 0 := by
      linarith [abs_nonneg (addressParameterDerivativeBound upper)]
    unfold incidenceSeparationRadius
    field_simp [denominator_ne] <;> ring
  constructor
  · have bound := weighted_sum_lt close.2.1 close.1
      (abs_nonneg (root other - root digits)) (constant := addressParameterDerivativeBound upper)
    rw [scale_identity] at bound
    simpa only [abs_sub_comm] using bound
  · have bound := weighted_sum_lt close.2.2 close.1
      (abs_nonneg (root other - root digits)) (constant := addressParameterDerivativeBound upper)
    rw [scale_identity] at bound
    simpa only [abs_sub_comm] using bound

/-- The manuscript's actual-cylinder incidence measure has the same exponent.
The fixed prefixes only change the radius by a fixed power of the lower parameter. -/
theorem cylinder_incidence_ball_mass {lower upper : ℝ} (lower_pos : 0 < lower)
    (upper_lt : upper < 1 / 2) (root : (ℕ → Bool × Bool) → ℝ)
    (root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper)
    (horizontalPrefix verticalPrefix : ℕ → Bool) (horizontalLength verticalLength : ℕ)
    (digits : ℕ → Bool × Bool) (depth : ℕ) :
    pairedAddressMeasure ((cylinderIncidencePoint root horizontalPrefix verticalPrefix
      horizontalLength verticalLength) ⁻¹'
      Metric.ball (cylinderIncidencePoint root horizontalPrefix verticalPrefix
        horizontalLength verticalLength digits)
        (incidenceSeparationRadius lower upper (max horizontalLength verticalLength + depth))) ≤
      (1 / 4 : ℝ≥0∞) ^ depth := by
  rw [← pairedPrefix_mass digits depth]
  apply measure_mono
  intro other close
  change dist (cylinderIncidencePoint root horizontalPrefix verticalPrefix
    horizontalLength verticalLength other) (cylinderIncidencePoint root horizontalPrefix verticalPrefix
    horizontalLength verticalLength digits) <
      incidenceSeparationRadius lower upper (max horizontalLength verticalLength + depth) at close
  simp only [cylinderIncidencePoint, Prod.dist_eq, Real.dist_eq, max_lt_iff] at close
  have scale_identity : (1 + |addressParameterDerivativeBound upper|) *
      incidenceSeparationRadius lower upper (max horizontalLength verticalLength + depth) =
        (1 - 2 * upper) * lower ^ (max horizontalLength verticalLength + depth) := by
    have denominator_ne : 1 + |addressParameterDerivativeBound upper| ≠ 0 := by
      linarith [abs_nonneg (addressParameterDerivativeBound upper)]
    unfold incidenceSeparationRadius
    field_simp [denominator_ne] <;> ring
  have first_close := weighted_sum_lt close.2.1 close.1
    (abs_nonneg (root other - root digits)) (constant := addressParameterDerivativeBound upper)
  have second_close := weighted_sum_lt close.2.2 close.1
    (abs_nonneg (root other - root digits)) (constant := addressParameterDerivativeBound upper)
  rw [scale_identity] at first_close second_close
  have first := close_incidence_same_prefix lower_pos upper_lt (root_in_band other)
    (root_in_band digits)
    (cylinderDigits horizontalPrefix horizontalLength (fun j => (other j).1))
    (cylinderDigits horizontalPrefix horizontalLength (fun j => (digits j).1))
    (max horizontalLength verticalLength + depth) first_close
  have second := close_incidence_same_prefix lower_pos upper_lt (root_in_band other)
    (root_in_band digits)
    (cylinderDigits verticalPrefix verticalLength (fun j => (other j).2))
    (cylinderDigits verticalPrefix verticalLength (fun j => (digits j).2))
    (max horizontalLength verticalLength + depth) second_close
  intro index before
  apply Prod.ext
  · simpa using first (horizontalLength + index) (by omega)
  · simpa using second (verticalLength + index) (by omega)

/-- All sufficiently small radii for the actual-cylinder incidence law. The
exponent is strictly greater than one when the band starts above one quarter.
The real-valued mass is legitimate because the source is a probability measure. -/
theorem cylinder_incidence_all_radius {lower upper : ℝ}
    (quarter_lt : 1 / 4 < lower) (upper_lt : upper < 1 / 2)
    (root : (ℕ → Bool × Bool) → ℝ)
    (root_in_band : ∀ digits, root digits ∈ Set.Icc lower upper)
    (horizontalPrefix verticalPrefix : ℕ → Bool) (horizontalLength verticalLength : ℕ)
    (digits : ℕ → Bool × Bool) {radius : ℝ} (radius_pos : 0 < radius)
    (radius_le : radius ≤ incidenceSeparationRadius lower upper
      (max horizontalLength verticalLength)) :
    pairedAddressMeasure.real
      ((cylinderIncidencePoint root horizontalPrefix verticalPrefix
        horizontalLength verticalLength) ⁻¹'
        Metric.ball (cylinderIncidencePoint root horizontalPrefix verticalPrefix
          horizontalLength verticalLength digits) radius) ≤
      (radius / (incidenceSeparationRadius lower upper
        (max horizontalLength verticalLength) * lower)) ^
          (Real.log 4 / Real.log (1 / lower)) := by
  have lower_pos : 0 < lower := by linarith
  have lower_lt_one : lower < 1 := by
    have band := root_in_band digits
    linarith [band.1, band.2]
  have scale_pos : 0 < incidenceSeparationRadius lower upper
      (max horizontalLength verticalLength) := by
    unfold incidenceSeparationRadius
    apply div_pos
    · exact mul_pos (by linarith) (pow_pos lower_pos _)
    · linarith [abs_nonneg (addressParameterDerivativeBound upper)]
  apply interpolate_geometric_mass
    (fun radius => pairedAddressMeasure.real
      ((cylinderIncidencePoint root horizontalPrefix verticalPrefix
        horizontalLength verticalLength) ⁻¹'
        Metric.ball (cylinderIncidencePoint root horizontalPrefix verticalPrefix
          horizontalLength verticalLength digits) radius))
    (fun _ _ comparison => measureReal_mono
      (Set.preimage_mono (Metric.ball_subset_ball comparison)))
    scale_pos lower_pos lower_lt_one
    (lt_trans zero_lt_one (incidence_exponent_gt_one quarter_lt lower_lt_one))
    radius_pos radius_le
  intro depth
  have scale_identity : incidenceSeparationRadius lower upper
      (max horizontalLength verticalLength) * lower ^ depth =
      incidenceSeparationRadius lower upper (max horizontalLength verticalLength + depth) := by
    unfold incidenceSeparationRadius
    rw [pow_add]
    ring
  rw [scale_identity, incidence_exponent_identity lower_pos lower_lt_one]
  have bound := cylinder_incidence_ball_mass lower_pos upper_lt root root_in_band
    horizontalPrefix verticalPrefix horizontalLength verticalLength digits depth
  have real_bound := ENNReal.toReal_mono (by finiteness) bound
  simpa only [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat] using real_bound

end LambdaCantor.First.Roots
