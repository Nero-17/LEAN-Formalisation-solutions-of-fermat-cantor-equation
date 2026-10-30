import LambdaCantor.First.ProjectionDistinct
import LambdaCantor.First.RootsMeasures
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

theorem paired_head_tail_independent :
    IndepFun (fun digits : ℕ → Bool × Bool => digits 0)
      (fun digits : ℕ → Bool × Bool => fun position : ℕ => digits (position + 1))
      Roots.pairedAddressMeasure := by
  have hindependent : iIndepFun (fun position (digits : ℕ → Bool × Bool) => digits position)
      Roots.pairedAddressMeasure :=
    iIndepFun_infinitePi (X := fun _ digit => digit) (by fun_prop)
  have hspaces : iIndep (fun position : ℕ => MeasurableSpace.comap
      (fun digits : ℕ → Bool × Bool => digits position) inferInstance)
      Roots.pairedAddressMeasure := hindependent
  have hsplit := indep_iSup_of_disjoint
    (fun position : ℕ => (measurable_pi_apply position).comap_le) hspaces
    (S := ({0} : Set ℕ)) (T := Set.range Nat.succ)
    (by simp [Set.disjoint_left])
  change Indep (MeasurableSpace.comap (fun digits : ℕ → Bool × Bool => digits 0) inferInstance)
    (MeasurableSpace.comap
      (fun digits : ℕ → Bool × Bool => fun position : ℕ => digits (position + 1)) inferInstance)
    Roots.pairedAddressMeasure
  apply indep_of_indep_of_le hsplit
  · exact le_iSup_of_le 0 (le_iSup_of_le (Set.mem_singleton 0) le_rfl)
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun position => le_iSup_of_le (position + 1)
      (le_iSup_of_le ⟨position, rfl⟩ le_rfl)

theorem paired_head_tail_law :
    Roots.pairedAddressMeasure.map
      (fun digits : ℕ → Bool × Bool => (digits 0, fun position : ℕ => digits (position + 1))) =
      (PMF.uniformOfFintype (Bool × Bool)).toMeasure.prod Roots.pairedAddressMeasure := by
  have hhead : Measurable (fun digits : ℕ → Bool × Bool => digits 0) :=
    measurable_pi_apply 0
  have htail : Measurable
      (fun digits : ℕ → Bool × Bool => fun position : ℕ => digits (position + 1)) :=
    measurable_pi_lambda _ (fun position => measurable_pi_apply (position + 1))
  rw [paired_head_tail_independent.map_prod_eq_prod_map_map
    hhead.aemeasurable htail.aemeasurable]
  unfold Roots.pairedAddressMeasure
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Nat.succ_injective]

def projectedAddress (ratio slope : ℝ) (digits : ℕ → Bool × Bool) : ℝ :=
  address ratio (fun position => (digits position).2) -
    slope * address ratio (fun position => (digits position).1)

theorem projectedAddress_measurable {ratio slope : ℝ} (hratio : 0 ≤ ratio)
    (hcontract : ratio < 1) : Measurable (projectedAddress ratio slope) := by
  have haddress := (continuous_address hratio hcontract).measurable
  exact (haddress.comp (by fun_prop)).sub (measurable_const.mul (haddress.comp (by fun_prop)))

def projectedMeasure (ratio slope : ℝ) : Measure ℝ :=
  Roots.pairedAddressMeasure.map (projectedAddress ratio slope)

theorem projectedMeasure_probability {ratio slope : ℝ} (hratio : 0 ≤ ratio)
    (hcontract : ratio < 1) : IsProbabilityMeasure (projectedMeasure ratio slope) :=
  Measure.isProbabilityMeasure_map (projectedAddress_measurable hratio hcontract).aemeasurable

theorem projectedAddress_first_digit {ratio slope : ℝ} (hratio : 0 ≤ ratio)
    (hcontract : ratio < 1) (digits : ℕ → Bool × Bool) :
    projectedAddress ratio slope digits =
      ratio * projectedAddress ratio slope (fun position => digits (position + 1)) +
        projectedDigit ratio slope (digitEquiv.symm (digits 0)) := by
  unfold projectedAddress projectedDigit
  rw [address_first_digit hratio hcontract (fun position => (digits position).2),
    address_first_digit hratio hcontract (fun position => (digits position).1)]
  simp only [Equiv.apply_symm_apply]
  ring

theorem uniform_paired_measure_eq_sum :
    (PMF.uniformOfFintype (Bool × Bool)).toMeasure =
      Measure.sum (fun digit : Bool × Bool => (4 : ℝ≥0∞)⁻¹ • Measure.dirac digit) := by
  rw [← Measure.sum_smul_dirac (PMF.uniformOfFintype (Bool × Bool)).toMeasure]
  congr 1
  funext digit
  simp [PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_prod]

theorem projectedMeasure_invariant {ratio slope : ℝ} (hratio : 0 ≤ ratio)
    (hcontract : ratio < 1) :
    ExternalProjection.IsFourMapInvariant (projectedMeasure ratio slope) ratio
      (projectedDigit ratio slope) := by
  let combine : (Bool × Bool) × (ℕ → Bool × Bool) → ℝ := fun pair =>
    ratio * projectedAddress ratio slope pair.2 +
      projectedDigit ratio slope (digitEquiv.symm pair.1)
  have hcombine : Measurable combine := by
    exact (measurable_const.mul
      ((projectedAddress_measurable hratio hcontract).comp measurable_snd)).add
      ((measurable_of_finite (fun digit : Bool × Bool =>
        projectedDigit ratio slope (digitEquiv.symm digit))).comp measurable_fst)
  have hmap : projectedMeasure ratio slope =
      ((PMF.uniformOfFintype (Bool × Bool)).toMeasure.prod Roots.pairedAddressMeasure).map
        combine := by
    rw [← paired_head_tail_law, Measure.map_map hcombine (by fun_prop)]
    unfold projectedMeasure
    congr 1
    funext digits
    exact projectedAddress_first_digit hratio hcontract digits
  unfold ExternalProjection.IsFourMapInvariant
  conv_lhs => rw [hmap]
  rw [uniform_paired_measure_eq_sum, Measure.prod_sum_left,
    Measure.map_sum hcombine.aemeasurable]
  simp_rw [Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map hcombine measurable_prodMk_left]
  rw [Measure.sum_fintype]
  have hterms : ∀ digit : Bool × Bool,
      Roots.pairedAddressMeasure.map (combine ∘ Prod.mk digit) =
      (projectedMeasure ratio slope).map
        (fun point : ℝ => ratio * point + projectedDigit ratio slope (digitEquiv.symm digit)) := by
    intro digit
    rw [projectedMeasure, Measure.map_map (by fun_prop)
      (projectedAddress_measurable hratio hcontract)]
    rfl
  simp_rw [hterms]
  simpa only [Equiv.symm_apply_apply] using
    (digitEquiv.sum_comp (fun digit : Bool × Bool =>
      (4 : ℝ≥0∞)⁻¹ • (projectedMeasure ratio slope).map
        (fun point : ℝ => ratio * point + projectedDigit ratio slope (digitEquiv.symm digit)))).symm

end LambdaCantor.First.PrefixSlopes
