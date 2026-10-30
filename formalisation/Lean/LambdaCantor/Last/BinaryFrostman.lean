import LambdaCantor.Last.BinaryPushforward
import LambdaCantor.Last.GeometricScale
import LambdaCantor.Last.ClosedMassDistribution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace LambdaCantor.Last

/-- Convert a geometric scale bound to the matching binary mass power bound. -/
theorem geometric_binary_mass_bound {ratio exponent constant diameter : ℝ}
    (hratio : 0 < ratio) (hexponent : 0 ≤ exponent)
    (hconstant : 0 ≤ constant) (hdiameter : 0 ≤ diameter)
    (hmatching : ratio ^ exponent = (1 / 2 : ℝ))
    {depth : ℕ} (hscale : ratio ^ depth ≤ constant * diameter) :
    (1 / 2 : ℝ) ^ depth ≤ constant ^ exponent * diameter ^ exponent := by
  rw [← hmatching, Real.rpow_pow_comm hratio.le]
  exact (Real.rpow_le_rpow (pow_nonneg hratio.le depth) hscale hexponent).trans_eq
    (Real.mul_rpow hconstant hdiameter)

/-- A separated binary coding has a Frostman bound, including diameter-zero sets. -/
theorem binary_pushforward_frostman
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (coding : (ℕ → Bool) → X) (hmeasurable : Measurable coding)
    (ratio separation exponent : ℝ)
    (hratio : 0 < ratio) (hratio_one : ratio < 1)
    (hseparation : 0 < separation) (hexponent : 0 < exponent)
    (hmatching : ratio ^ exponent = (1 / 2 : ℝ))
    (hseparated : ∀ depth : ℕ, ∀ first second : ℕ → Bool,
      (∃ position < depth, first position ≠ second position) →
      ENNReal.ofReal (separation * ratio ^ depth) ≤ edist (coding first) (coding second))
    {subset : Set X} (hsubset : MeasurableSet subset)
    (hsmall : ediam subset ≤ ENNReal.ofReal (separation / 2)) :
    binaryBranchMeasure.map coding subset ≤
      ENNReal.ofReal ((2 / (separation * ratio)) ^ exponent) * ediam subset ^ exponent := by
  have hfinite : ediam subset ≠ ∞ := ne_of_lt (hsmall.trans_lt ENNReal.ofReal_lt_top)
  by_cases hzero : ediam subset = 0
  · have hmass : binaryBranchMeasure.map coding subset ≤ 0 := by
      apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (2 : ℝ≥0∞)⁻¹) (by norm_num))
      apply Filter.Eventually.of_forall
      intro depth
      apply binary_pushforward_small_set_bound coding hmeasurable depth
        (ENNReal.ofReal (separation * ratio ^ depth)) (hseparated depth) hsubset
      rw [hzero]
      exact ENNReal.ofReal_pos.mpr (mul_pos hseparation (pow_pos hratio depth))
    exact hmass.trans bot_le
  · have hdiameter : 0 < (ediam subset).toReal := ENNReal.toReal_pos hzero hfinite
    have hsmallReal : (ediam subset).toReal ≤ separation / 2 := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall
      simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ separation / 2)] using h
    obtain ⟨depth, hstrict, hscale⟩ :=
      exists_geometric_depth hratio hratio_one hseparation hdiameter hsmallReal
    have hbound := binary_pushforward_small_set_bound coding hmeasurable depth
      (ENNReal.ofReal (separation * ratio ^ depth)) (hseparated depth) hsubset
      (by
        rw [← ENNReal.ofReal_toReal hfinite]
        exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos hseparation (pow_pos hratio depth))).mpr hstrict)
    have hreal := geometric_binary_mass_bound hratio hexponent.le
      (by positivity : 0 ≤ 2 / (separation * ratio)) hdiameter.le hmatching hscale
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    have hboundReal : binaryBranchMeasure.map coding subset ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ depth) := by
      simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), hhalf] using hbound
    apply hboundReal.trans
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      ← ENNReal.ofReal_rpow_of_nonneg hdiameter.le hexponent.le,
      ENNReal.ofReal_toReal hfinite] at h
    exact h

end LambdaCantor.Last
