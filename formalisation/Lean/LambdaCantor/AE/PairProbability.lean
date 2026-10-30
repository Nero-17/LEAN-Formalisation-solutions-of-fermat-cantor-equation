import LambdaCantor.AE.AddressPairKernel
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace LambdaCantor.AE

/-- One simultaneous digit of the four independent addresses. -/
abbrev FourDigits := Fin 4 → Bool

abbrev equalPairDigits : Set FourDigits :=
  {digits | (digits 0).toNat + (digits 1).toNat =
    (digits 2).toNat + (digits 3).toNat}

def fourDigitMeasure : Measure FourDigits := (PMF.uniformOfFintype FourDigits).toMeasure

instance : IsProbabilityMeasure fourDigitMeasure := by
  unfold fourDigitMeasure
  infer_instance

def fourAddressMeasure : Measure (ℕ → FourDigits) :=
  Measure.infinitePi (fun _ : ℕ => fourDigitMeasure)

instance : IsProbabilityMeasure fourAddressMeasure := by
  unfold fourAddressMeasure
  infer_instance

theorem card_equalPairDigits : Fintype.card equalPairDigits = 6 := by decide

theorem fourDigitMeasure_equalPairDigits :
    fourDigitMeasure equalPairDigits = (3 / 8 : ℝ≥0∞) := by
  rw [fourDigitMeasure, PMF.toMeasure_uniformOfFintype_apply equalPairDigits
    (Set.toFinite equalPairDigits).measurableSet]
  have total_card : Fintype.card FourDigits = 16 := by decide
  rw [card_equalPairDigits, total_card]
  exact (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr (by norm_num)

/-- The actual four-address product event that all earlier convolution digits agree. -/
def prefixPairAgreement (depth : ℕ) : Set (ℕ → FourDigits) :=
  Set.pi (Finset.range depth : Set ℕ) (fun _ => equalPairDigits)

theorem measure_prefixPairAgreement (depth : ℕ) :
    fourAddressMeasure (prefixPairAgreement depth) = (3 / 8 : ℝ≥0∞) ^ depth := by
  unfold fourAddressMeasure prefixPairAgreement
  rw [Measure.infinitePi_pi (fun _ : ℕ => fourDigitMeasure)
    (s := Finset.range depth) (t := fun _ => equalPairDigits)
    (fun _ _ => (Set.toFinite equalPairDigits).measurableSet)]
  simp [fourDigitMeasure_equalPairDigits]

theorem pairDigitDifference_eq_zero_iff (sample : ℕ → FourDigits) (index : ℕ) :
    pairDigitDifference (fun n => sample n 0) (fun n => sample n 1)
      (fun n => sample n 2) (fun n => sample n 3) index = 0 ↔
    sample index ∈ equalPairDigits := by
  have digit_equivalence (first second third fourth : Bool) :
      (if first then (1 : ℝ) else 0) + (if second then 1 else 0) -
        ((if third then 1 else 0) + (if fourth then 1 else 0)) = 0 ↔
      first.toNat + second.toNat = third.toNat + fourth.toNat := by
    cases first <;> cases second <;> cases third <;> cases fourth <;> norm_num
  exact digit_equivalence (sample index 0) (sample index 1) (sample index 2) (sample index 3)

theorem mem_prefixPairAgreement_iff (sample : ℕ → FourDigits) (depth : ℕ) :
    sample ∈ prefixPairAgreement depth ↔
      ∀ index < depth, pairDigitDifference (fun n => sample n 0) (fun n => sample n 1)
        (fun n => sample n 2) (fun n => sample n 3) index = 0 := by
  simp only [prefixPairAgreement, Set.mem_pi, Finset.mem_coe, Finset.mem_range,
    pairDigitDifference_eq_zero_iff]

def firstPairDifference (depth : ℕ) : Set (ℕ → FourDigits) :=
  prefixPairAgreement depth ∩ {sample | sample depth ∉ equalPairDigits}

/-- The geometric majorant used when integrating the actual pairwise estimate. -/
theorem measure_firstPairDifference_le (depth : ℕ) :
    fourAddressMeasure (firstPairDifference depth) ≤ (3 / 8 : ℝ≥0∞) ^ depth := by
  rw [← measure_prefixPairAgreement]
  exact measure_mono Set.inter_subset_left

theorem firstPairDifference_has_leading_digit {sample : ℕ → FourDigits} {depth : ℕ}
    (hsample : sample ∈ firstPairDifference depth) :
    (∀ index < depth, pairDigitDifference (fun n => sample n 0) (fun n => sample n 1)
      (fun n => sample n 2) (fun n => sample n 3) index = 0) ∧
    pairDigitDifference (fun n => sample n 0) (fun n => sample n 1)
      (fun n => sample n 2) (fun n => sample n 3) depth ≠ 0 := by
  exact ⟨(mem_prefixPairAgreement_iff sample depth).mp hsample.1,
    fun hequal => hsample.2 ((pairDigitDifference_eq_zero_iff sample depth).mp hequal)⟩

/-- The exceptional pairs whose convolution digits agree forever have zero mass. -/
theorem measure_allPairAgreement :
    fourAddressMeasure {sample | ∀ index, sample index ∈ equalPairDigits} = 0 := by
  apply le_antisymm _ bot_le
  apply ge_of_tendsto
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (3 / 8 : ℝ≥0∞) < 1 by
        exact (ENNReal.div_lt_iff (by norm_num) (by norm_num)).mpr (by norm_num)))
  apply Filter.Eventually.of_forall
  intro depth
  rw [← measure_prefixPairAgreement]
  apply measure_mono
  intro sample hsample index _
  exact hsample index

theorem firstPairDifference_pairwiseDisjoint :
    Pairwise (fun firstDepth secondDepth : ℕ =>
      Disjoint (firstPairDifference firstDepth) (firstPairDifference secondDepth)) := by
  intro firstDepth secondDepth hne
  apply Set.disjoint_left.mpr
  intro sample hfirst hsecond
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hfirst.2 (hsecond.1 firstDepth (Finset.mem_range.mpr hlt))
  · exact hsecond.2 (hfirst.1 secondDepth (Finset.mem_range.mpr hgt))

theorem exists_firstPairDifference_iff (sample : ℕ → FourDigits) :
    (∃ depth, sample ∈ firstPairDifference depth) ↔
      ¬ ∀ index, sample index ∈ equalPairDigits := by
  classical
  constructor
  · rintro ⟨depth, hdepth⟩ hall
    exact hdepth.2 (hall depth)
  · intro hnotall
    have hexists : ∃ index, sample index ∉ equalPairDigits := not_forall.mp hnotall
    refine ⟨Nat.find hexists, ?_, Nat.find_spec hexists⟩
    intro index hindex
    exact not_not.mp (Nat.find_min hexists (Finset.mem_range.mp hindex))

theorem ae_exists_firstPairDifference :
    ∀ᵐ sample ∂fourAddressMeasure, ∃ depth, sample ∈ firstPairDifference depth := by
  rw [ae_iff]
  simpa only [exists_firstPairDifference_iff, not_not] using measure_allPairAgreement

end LambdaCantor.AE
