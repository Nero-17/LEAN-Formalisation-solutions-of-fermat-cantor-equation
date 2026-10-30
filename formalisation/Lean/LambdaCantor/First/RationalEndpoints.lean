import LambdaCantor.First.RootsMain
import LambdaCantor.First.RootFibreConsequences
import LambdaCantor.First.RealNormalizationAdapter
import LambdaCantor.First.RationalRootFibreAdapter
import LambdaCantor.First.RationalPowerFourData
import LambdaCantor.First.RationalContinuity
import LambdaCantor.First.Upper

noncomputable section
open MeasureTheory Set Filter Topology
namespace LambdaCantor.First

/-- Every nonempty open parameter interval above one quarter carries a
positive Lebesgue measure set of positive-dimensional irrational-exponent fibres. -/
theorem irrational_parameters {exponent lower upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hlower : (1 / 4 : ℝ) ≤ lower) (hordered : lower < upper)
    (hupper : upper ≤ 1 / 2) :
    0 < volume {ratio : ℝ | ratio ∈ Ioo lower upper ∧
      0 < dimH (intersection exponent ratio)} := by
  obtain ⟨data, hdataLower, hdataUpper⟩ := Roots.irrational_rootFibreData
    (lower := (2 * lower + upper) / 3) (target := (lower + upper) / 2)
    (upper := (lower + 2 * upper) / 3) hirrational hexponent
    (by linarith) (by linarith) (by linarith) (by linarith)
  apply (Roots.rootFibreConclusion_positive_volume_band data (Roots.root_fibres data)).trans_le
  apply measure_mono
  intro ratio hratio
  refine ⟨⟨?_, ?_⟩, hratio.2⟩
  · rw [hdataLower] at hratio
    linarith [hratio.1.1]
  · rw [hdataUpper] at hratio
    linarith [hratio.1.2]

/-- The first Hausdorff transition for every irrational exponent above one
is exactly one quarter. -/
theorem irrational_onset {exponent : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent) :
    firstTransition exponent = 1 / 4 := by
  apply first_eq_quarter_of_parameters exponent (first_lower hexponent)
  intro upper hlower hupper
  have positive := irrational_parameters hirrational hexponent (le_refl (1 / 4 : ℝ)) hlower hupper.le
  obtain ⟨ratio, hratio, hdimension⟩ :=
    nonempty_of_measure_ne_zero volume _ positive.ne'
  exact ⟨ratio, hratio.1, hratio.2, hdimension⟩

/-- Quantitative denominator bound for every reduced positive rational exponent. -/
theorem denominator (numerator denominator : ℕ)
    (hnumerator : 0 < numerator) (hdenominator : 0 < denominator)
    (hcoprime : numerator.Coprime denominator)
    (hexponent : 2 ≤ (numerator : ℝ) / denominator) :
    0 ≤ firstTransition ((numerator : ℝ) / denominator) - 1 / 4 ∧
      firstTransition ((numerator : ℝ) / denominator) - 1 / 4 ≤
        (3 / 2 : ℝ) ^ ((numerator : ℝ) / denominator) * Real.log 4 /
          (2 * ((numerator : ℝ) / denominator) * denominator) := by
  refine ⟨sub_nonneg.mpr (first_lower (by linarith)), ?_⟩
  obtain ⟨target, htarget, hbound, hdata⟩ :=
    Roots.rational_denominator_rootFibreData numerator denominator hnumerator hdenominator
      hcoprime hexponent
  have htransition : firstTransition ((numerator : ℝ) / denominator) ≤ target := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro ceiling hceiling
    let upper : ℝ := min ceiling ((target + 1 / 2) / 2)
    have hupperTarget : target < upper := lt_min hceiling (by linarith [htarget.2])
    have hupperHalf : upper < 1 / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith [htarget.2])
    obtain ⟨data, _, hupper⟩ := hdata ((1 / 4 + target) / 2) upper
      (by linarith [htarget.1]) (by linarith [htarget.1]) hupperTarget hupperHalf
    have hle := Roots.rootFibreConclusion_firstTransition_le_upper data (Roots.root_fibres data)
    rw [hupper] at hle
    exact hle.trans (min_le_left _ _)
  linarith

/-- The denominator bound in the canonical reduced representation of a rational. -/
theorem denominator_rat (exponent : ℚ) (hexponent : 2 ≤ (exponent : ℝ)) :
    firstTransition exponent - 1 / 4 ≤
      (3 / 2 : ℝ) ^ (exponent : ℝ) * Real.log 4 /
        (2 * (exponent : ℝ) * exponent.den) := by
  have hpositive : (0 : ℚ) < exponent := by exact_mod_cast (show (0 : ℝ) < exponent by linarith)
  have hnumerator : 0 < exponent.num := Rat.num_pos.mpr hpositive
  have habs : (exponent.num.natAbs : ℤ) = exponent.num := by
    simpa only [abs_of_pos hnumerator] using Int.natCast_natAbs exponent.num
  have hcast : (exponent.num.natAbs : ℝ) = (exponent.num : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun value : ℤ => (value : ℝ)) habs
  have hrepresentation : (exponent.num.natAbs : ℝ) / exponent.den = (exponent : ℝ) := by
    rw [hcast, Rat.cast_def]
  have hnumeratorNat : 0 < exponent.num.natAbs := by
    have : (0 : ℤ) < exponent.num.natAbs := by rw [habs]; exact hnumerator
    exact_mod_cast this
  have hbound := (denominator exponent.num.natAbs exponent.den hnumeratorNat exponent.den_pos
    exponent.reduced (by rwa [hrepresentation])).2
  simpa only [hrepresentation] using hbound

/-- The punctured first-transition limit at every exponent on the exponent
half-line is one quarter. -/
theorem punctured_limit (center : ℝ) :
    Tendsto firstTransition
      (𝓝[{exponent : ℝ | 2 ≤ exponent ∧ exponent ≠ center}] center) (𝓝 (1 / 4)) := by
  apply first_punctured_limit_of_onset_bounds
    (fun exponent hexponent => first_lower (by linarith)) _ denominator_rat center
  intro exponent hexponent hnonrational
  apply irrational_onset _ (by linarith)
  intro hrational
  obtain ⟨rational, hequal⟩ := hrational
  exact hnonrational rational hequal.symm

/-- Continuity on the exponent half-line occurs exactly at exponents whose
first transition is one quarter. -/
theorem continuity_iff_quarter {exponent : ℝ} (hexponent : 2 ≤ exponent) :
    ContinuousWithinAt firstTransition (Ici 2) exponent ↔ firstTransition exponent = 1 / 4 :=
  continuousWithinAt_iff_of_punctured_limit firstTransition (1 / 4) exponent hexponent
    (punctured_limit exponent)

/-- Every positive integral power of four has first transition one quarter. -/
theorem powers_four (phase : ℕ) (hphase : 1 ≤ phase) :
    firstTransition ((4 ^ phase : ℕ) : ℝ) = 1 / 4 := by
  have hexponent : (1 : ℝ) < (4 ^ phase : ℕ) := by
    have hfour : 4 ≤ (4 : ℕ) ^ phase := by
      simpa using pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℕ)) hphase
    exact_mod_cast (show 1 < (4 : ℕ) ^ phase by omega)
  apply first_eq_quarter_of_parameters _ (first_lower hexponent)
  intro upper hlower hupper
  obtain ⟨data, hdata⟩ := Roots.powersFour_rootFibreData phase hphase hlower hupper
  obtain ⟨ratio, hratio, hdimension⟩ :=
    Roots.rootFibreConclusion_exists_positive_band data (Roots.root_fibres data)
  exact ⟨ratio, data.lower_gt_quarter.trans_le hratio.1, hratio.2.trans_lt hdata, hdimension⟩

end LambdaCantor.First
