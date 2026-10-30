import LambdaCantor.First.SobolevEnergyContinuity
import LambdaCantor.First.RootsStateNull

noncomputable section
open MeasureTheory
open scoped ENNReal Topology
namespace LambdaCantor.First.Roots

theorem projectedSobolevEnergy_mono_order (parameter : ℝ × ℝ)
    {first second : ℝ} (ordered : first ≤ second) :
    projectedSobolevEnergy first parameter ≤ projectedSobolevEnergy second parameter := by
  apply lintegral_mono
  intro frequency
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg frequency]) ordered

def rootSobolevGoodSet {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) : Set (ℕ → Bool × Bool) :=
  {digits | projectedSobolevEnergy (1 / ((orderIndex : ℝ) + 1))
    (rootFibreState data digits) ≤ bound}

theorem rootFibreData_compact_good_set {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) : IsCompact (rootSobolevGoodSet data orderIndex bound) := by
  let bandState : (ℕ → Bool × Bool) → Set.Icc data.lower data.upper × ℝ :=
    fun digits => (⟨data.root digits, data.root_in_band digits⟩, (rootFibreState data digits).2)
  have continuous_bandState : Continuous bandState :=
    ((rootFibreData_continuous_root data).subtype_mk data.root_in_band).prodMk
      (continuous_snd.comp (rootFibreData_continuous_state data))
  have energy := lowerSemicontinuous_projectedSobolevEnergy_band
    (by linarith [data.lower_gt_quarter] : 0 ≤ data.lower)
    (by linarith [data.upper_lt_half] : data.upper < 1) data.ordered
    (1 / ((orderIndex : ℝ) + 1))
  exact ((energy.comp_continuous continuous_bandState).isClosed_preimage (bound : ℝ≥0∞)).isCompact

/-- Every actual finite positive-order state energy lies in one of a
countable family of compact address sets with a common order and bound. -/
theorem rootFibreData_good_sets_cover_finite_energy {exponent : ℝ}
    (data : RootFibreData exponent) (digits : ℕ → Bool × Bool)
    (finite_energy : ∃ order : ℝ, 0 < order ∧
      projectedSobolevEnergy order (rootFibreState data digits) ≠ ∞) :
    ∃ orderIndex bound : ℕ, digits ∈ rootSobolevGoodSet data orderIndex bound := by
  obtain ⟨order, positive, finite⟩ := finite_energy
  obtain ⟨orderIndex, smaller⟩ := exists_nat_one_div_lt positive
  have finite_smaller : projectedSobolevEnergy (1 / ((orderIndex : ℝ) + 1))
      (rootFibreState data digits) ≠ ∞ :=
    ne_top_of_le_ne_top finite (projectedSobolevEnergy_mono_order _ smaller.le)
  obtain ⟨bound, bound_gt⟩ := ENNReal.exists_nat_gt finite_smaller
  exact ⟨orderIndex, bound, bound_gt.le⟩

theorem rootFibreData_good_set_uniform_energy {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    0 < 1 / ((orderIndex : ℝ) + 1) ∧
      ∀ digits ∈ rootSobolevGoodSet data orderIndex bound,
        projectedSobolevEnergy (1 / ((orderIndex : ℝ) + 1))
          (rootFibreState data digits) ≤ bound := by
  constructor
  · positivity
  · intro digits member; exact member

end LambdaCantor.First.Roots
