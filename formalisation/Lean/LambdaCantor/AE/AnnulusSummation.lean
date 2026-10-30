import LambdaCantor.AE.KernelConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace LambdaCantor.AE

/-- The interval-dependent growth ratio lies in the range used by interpolation. -/
theorem annulus_growth_gt_four {lower upper : ℝ}
    (hlower : 0 < lower) (horder : lower ≤ upper) (hupper : upper < 1 / 2) :
    4 < upper / lower ^ 3 := by
  apply (lt_div_iff₀ (pow_pos hlower 3)).mpr
  have hsquare : lower ^ 2 < 1 / 4 := by
    nlinarith [mul_pos (show 0 < 1 / 2 + lower by linarith)
      (show 0 < 1 / 2 - lower by linarith)]
  have hcube := mul_lt_mul_of_pos_right hsquare hlower
  nlinarith

/-- Interpolation of two positive upper bounds. -/
theorem min_le_interpolated {first second weight : ℝ}
    (hfirst : 0 < first) (hsecond : 0 < second)
    (hweight : 0 ≤ weight) (hweight_one : weight ≤ 1) :
    min first second ≤ first ^ (1 - weight) * second ^ weight := by
  have hmin : 0 < min first second := lt_min hfirst hsecond
  calc
    min first second = (min first second) ^ (1 - weight) * (min first second) ^ weight := by
      rw [← Real.rpow_add hmin]
      simp
    _ ≤ first ^ (1 - weight) * second ^ weight :=
      mul_le_mul (Real.rpow_le_rpow hmin.le (min_le_left _ _) (by linarith))
        (Real.rpow_le_rpow hmin.le (min_le_right _ _) hweight)
        (Real.rpow_nonneg hmin.le _) (Real.rpow_nonneg hfirst.le _)

/-- Interpolating the trivial and cancellation estimates gives a power of the frequency. -/
theorem min_annulus_le {frequency amplitude weight : ℝ}
    (hfrequency : 0 < frequency) (hamplitude : 0 < amplitude)
    (hweight : 0 ≤ weight) (hweight_one : weight ≤ 1) :
    min frequency (amplitude / frequency) ≤
      frequency ^ (1 - 2 * weight) * amplitude ^ weight := by
  have hbound := min_le_interpolated hfrequency (div_pos hamplitude hfrequency)
    hweight hweight_one
  rw [Real.div_rpow hamplitude.le hfrequency.le] at hbound
  calc
    min frequency (amplitude / frequency) ≤
        frequency ^ (1 - weight) * (amplitude ^ weight / frequency ^ weight) := hbound
    _ = (frequency ^ (1 - weight) / frequency ^ weight) * amplitude ^ weight := by ring
    _ = frequency ^ (1 - 2 * weight) * amplitude ^ weight := by
      rw [← Real.rpow_sub hfrequency]
      congr 2
      ring

/-- The first-difference-depth majorant is summable whenever its geometric ratio is below one. -/
theorem summable_interpolated_depth_majorant (degree : ℕ)
    {probability growth weight : ℝ} (hprobability : 0 < probability)
    (hgrowth : 0 < growth) (hdecay : probability * growth ^ weight < 1) :
    Summable (fun depth : ℕ => ((depth + 1 : ℕ) : ℝ) ^ degree *
      (probability * growth ^ weight) ^ depth) := by
  simpa only [Nat.zero_add] using summable_shifted_polynomial_geometric 0 degree
    (mul_pos hprobability (Real.rpow_pos_of_pos hgrowth _)) hdecay

theorem annulus_depth_term_le (depth degree : ℕ)
    {probability growth frequency weight : ℝ}
    (hprobability : 0 ≤ probability) (hgrowth : 0 < growth)
    (hfrequency : 0 < frequency) (hweight : 0 ≤ weight) (hweight_one : weight ≤ 1) :
    probability ^ depth * min frequency
      ((((depth + 1 : ℕ) : ℝ) ^ degree * growth ^ depth) / frequency) ≤
    frequency ^ (1 - 2 * weight) *
      (((depth + 1 : ℕ) : ℝ) ^ degree * (probability * growth ^ weight) ^ depth) := by
  have hpolynomial : 1 ≤ ((depth + 1 : ℕ) : ℝ) ^ degree :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ depth + 1 by omega))
  have hpolynomialPositive : 0 < ((depth + 1 : ℕ) : ℝ) ^ degree := by linarith
  have hpolynomialPower : (((depth + 1 : ℕ) : ℝ) ^ degree) ^ weight ≤
      ((depth + 1 : ℕ) : ℝ) ^ degree := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hpolynomial hweight_one
  have hgrowthPower : (growth ^ depth) ^ weight = (growth ^ weight) ^ depth := by
    rw [← Real.rpow_natCast_mul hgrowth.le, ← Real.rpow_mul_natCast hgrowth.le]
    congr 1
    ring
  have hinterpolation := min_annulus_le hfrequency
    (mul_pos hpolynomialPositive (pow_pos hgrowth depth)) hweight hweight_one
  rw [Real.mul_rpow hpolynomialPositive.le (pow_nonneg hgrowth.le _), hgrowthPower] at hinterpolation
  calc
    probability ^ depth * min frequency
        ((((depth + 1 : ℕ) : ℝ) ^ degree * growth ^ depth) / frequency) ≤
        probability ^ depth * (frequency ^ (1 - 2 * weight) *
          ((((depth + 1 : ℕ) : ℝ) ^ degree) ^ weight * (growth ^ weight) ^ depth)) :=
      mul_le_mul_of_nonneg_left hinterpolation (pow_nonneg hprobability _)
    _ ≤ probability ^ depth * (frequency ^ (1 - 2 * weight) *
          (((depth + 1 : ℕ) : ℝ) ^ degree * (growth ^ weight) ^ depth)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpolynomialPower
            (pow_nonneg (Real.rpow_nonneg hgrowth.le _) _))
          (Real.rpow_nonneg hfrequency.le _)) (pow_nonneg hprobability _)
    _ = _ := by rw [mul_pow]; ring

/-- Sum the actual numerical first-difference majorant with the full polynomial factor. -/
theorem annulus_series_bound (degree : ℕ)
    {probability growth frequency weight : ℝ}
    (hprobability : 0 < probability) (hgrowth : 0 < growth)
    (hfrequency : 0 < frequency) (hweight : 0 ≤ weight) (hweight_one : weight ≤ 1)
    (hdecay : probability * growth ^ weight < 1) :
    (∑' depth : ℕ, probability ^ depth * min frequency
      ((((depth + 1 : ℕ) : ℝ) ^ degree * growth ^ depth) / frequency)) ≤
    frequency ^ (1 - 2 * weight) *
      ∑' depth : ℕ, ((depth + 1 : ℕ) : ℝ) ^ degree *
        (probability * growth ^ weight) ^ depth := by
  have hmajorant := (summable_interpolated_depth_majorant degree hprobability hgrowth hdecay).mul_left
    (frequency ^ (1 - 2 * weight))
  have hsum := Summable.of_nonneg_of_le
    (fun depth : ℕ => mul_nonneg (pow_nonneg hprobability.le _)
      (le_min hfrequency.le (div_nonneg (mul_nonneg
        (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hgrowth.le _)) hfrequency.le)))
    (fun depth => annulus_depth_term_le depth degree hprobability.le hgrowth hfrequency hweight hweight_one)
    hmajorant
  simpa only [tsum_mul_left] using Summable.tsum_le_tsum
    (fun depth => annulus_depth_term_le depth degree hprobability.le hgrowth hfrequency hweight hweight_one)
    hsum hmajorant

/-- Strict room in the Sobolev exponent makes the weighted dyadic frequency powers summable. -/
theorem summable_sobolev_dyadic_powers {weight regularity : ℝ}
    (hroom : 2 * regularity < 2 * weight - 1) :
    Summable (fun scale : ℕ => ((2 : ℝ) ^ scale) ^ (2 * regularity) *
      ((2 : ℝ) ^ scale) ^ (1 - 2 * weight)) := by
  have hratio : (2 : ℝ) ^ (2 * regularity + (1 - 2 * weight)) < 1 := by
    convert Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (show 2 * regularity + (1 - 2 * weight) < 0 by linarith) using 1 <;> norm_num
  have hsum : Summable (fun scale : ℕ =>
      ((2 : ℝ) ^ (2 * regularity + (1 - 2 * weight))) ^ scale) :=
    summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hratio
  apply hsum.congr
  intro scale
  rw [← Real.rpow_add (pow_pos (by norm_num : (0 : ℝ) < 2) scale),
    ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

/-- Every exponent in the paper's strict logarithmic range admits a summable interpolation weight. -/
theorem exists_sobolev_interpolation_weight {growth regularity : ℝ}
    (hgrowth : (8 / 3 : ℝ) < growth) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity < 2 * Real.log (8 / 3 : ℝ) / Real.log growth - 1) :
    ∃ weight : ℝ, 0 < weight ∧ weight < 1 ∧
      (3 / 8 : ℝ) * growth ^ weight < 1 ∧ 2 * regularity < 2 * weight - 1 := by
  have hbase : 1 < growth := by linarith
  have hlog : 0 < Real.log growth := Real.log_pos hbase
  have hupper : Real.log (8 / 3 : ℝ) / Real.log growth < 1 :=
    (div_lt_one hlog).mpr (Real.log_lt_log (by norm_num) hgrowth)
  have hinterval : (2 * regularity + 1) / 2 <
      Real.log (8 / 3 : ℝ) / Real.log growth := by
    have hrearrange : 2 * Real.log (8 / 3 : ℝ) / Real.log growth =
        2 * (Real.log (8 / 3 : ℝ) / Real.log growth) := by ring
    rw [hrearrange] at hrange
    linarith
  obtain ⟨weight, hlower, hweight⟩ := exists_between hinterval
  have hidentity : growth ^ (Real.log (8 / 3 : ℝ) / Real.log growth) = 8 / 3 := by
    rw [Real.rpow_def_of_pos (by linarith)]
    have hcancel : Real.log growth * (Real.log (8 / 3 : ℝ) / Real.log growth) =
        Real.log (8 / 3 : ℝ) := by field_simp [ne_of_gt hlog]
    rw [hcancel, Real.exp_log (by norm_num)]
  have hpower := Real.rpow_lt_rpow_of_exponent_lt hbase hweight
  rw [hidentity] at hpower
  exact ⟨weight, by linarith, hweight.trans hupper, by nlinarith, by linarith⟩

/-- The exact numerical double sum produced by the pair estimate is Sobolev-summable
throughout the paper's strict exponent range. -/
theorem summable_weighted_annulus_series (degree : ℕ) {growth regularity : ℝ}
    (hgrowth : (8 / 3 : ℝ) < growth) (hregularity : 0 ≤ regularity)
    (hrange : 2 * regularity < 2 * Real.log (8 / 3 : ℝ) / Real.log growth - 1) :
    Summable (fun scale : ℕ => ((2 : ℝ) ^ scale) ^ (2 * regularity) *
      ∑' depth : ℕ, (3 / 8 : ℝ) ^ depth * min ((2 : ℝ) ^ scale)
        ((((depth + 1 : ℕ) : ℝ) ^ degree * growth ^ depth) / (2 : ℝ) ^ scale)) := by
  obtain ⟨weight, hweight, hweight_one, hdecay, hroom⟩ :=
    exists_sobolev_interpolation_weight hgrowth hregularity hrange
  have hmajorant := (summable_sobolev_dyadic_powers hroom).mul_right
    (∑' depth : ℕ, ((depth + 1 : ℕ) : ℝ) ^ degree *
      ((3 / 8 : ℝ) * growth ^ weight) ^ depth)
  apply Summable.of_nonneg_of_le ?_ ?_ hmajorant
  · intro scale
    apply mul_nonneg (Real.rpow_nonneg (pow_nonneg (by norm_num) _) _)
    apply tsum_nonneg
    intro depth
    apply mul_nonneg (pow_nonneg (by norm_num) _)
    apply le_min (pow_nonneg (by norm_num) _)
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (pow_nonneg (by linarith) _)) (pow_nonneg (by norm_num) _)
  · intro scale
    have hbound := mul_le_mul_of_nonneg_left
      (annulus_series_bound degree (by norm_num : (0 : ℝ) < 3 / 8)
        (by linarith : 0 < growth) (pow_pos (by norm_num : (0 : ℝ) < 2) scale)
        hweight.le hweight_one.le hdecay)
      (Real.rpow_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) scale) (2 * regularity))
    simpa only [mul_assoc] using hbound

end LambdaCantor.AE
