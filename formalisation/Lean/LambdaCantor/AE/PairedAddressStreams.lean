import LambdaCantor.AE.AddressProbability
import LambdaCantor.First.RootsMeasures
import Mathlib.Probability.Independence.InfinitePi

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LambdaCantor.AE

theorem fair_paired_digit_product : (PMF.uniformOfFintype (Bool × Bool)).toMeasure =
    fairDigitMeasure.prod fairDigitMeasure := by
  apply Measure.ext_of_singleton
  intro pair
  have singleton : ({pair} : Set (Bool × Bool)) = ({pair.1} : Set Bool) ×ˢ ({pair.2} : Set Bool) := by
    ext point
    simp only [Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff]
  rw [singleton, Measure.prod_prod, ← singleton]
  simp [fairDigitMeasure, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_prod]
  change (4 : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹*(2 : ℝ≥0∞)⁻¹
  calc
    _ = ((2 : ℝ≥0∞)*2)⁻¹ := by norm_num
    _ = _ := ENNReal.mul_inv (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
      (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))

theorem flat_bits_paired_address_law :
    (Measure.infinitePi (fun _ : ℕ × Bool => fairDigitMeasure)).map
      (fun bits index => (bits (index, false), bits (index, true))) =
      First.Roots.pairedAddressMeasure := by
  have pair_law := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => fairDigitMeasure) (by decide : false ≠ true)
  have curried := Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Bool) => fairDigitMeasure)
  have mapped := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => Measure.infinitePi (fun _ : Bool => fairDigitMeasure))
    (f := fun _ bits => (bits false, bits true)) (by fun_prop)
  rw [pair_law, ← fair_paired_digit_product] at mapped
  rw [← curried, Measure.map_map (by fun_prop) (by fun_prop)] at mapped
  exact mapped

theorem paired_address_streams_independent :
    IndepFun (fun digits : ℕ → Bool × Bool => fun index => (digits index).1)
      (fun digits : ℕ → Bool × Bool => fun index => (digits index).2)
      First.Roots.pairedAddressMeasure := by
  let flat : Measure ((ℕ × Bool) → Bool) := Measure.infinitePi (fun _ : ℕ × Bool => fairDigitMeasure)
  have independent : iIndepFun (fun position (bits : (ℕ × Bool) → Bool) => bits position) flat :=
    iIndepFun_infinitePi (X := fun _ bit => bit) (by fun_prop)
  have split := indep_iSup_of_disjoint
    (fun position : ℕ × Bool => (measurable_pi_apply position).comap_le) independent
    (S := {position | position.2 = false}) (T := {position | position.2 = true})
    (by simp [Set.disjoint_left])
  have streams : IndepFun (fun bits : (ℕ × Bool) → Bool => fun index => bits (index, false))
      (fun bits : (ℕ × Bool) → Bool => fun index => bits (index, true)) flat := by
    change Indep _ _ flat
    apply indep_of_indep_of_le split
    · rw [MeasurableSpace.comap_process_pi]
      exact iSup_le fun index => le_iSup_of_le (index, false) (le_iSup_of_le rfl le_rfl)
    · rw [MeasurableSpace.comap_process_pi]
      exact iSup_le fun index => le_iSup_of_le (index, true) (le_iSup_of_le rfl le_rfl)
  have first_measurable : Measurable
      (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) :=
    measurable_pi_lambda _ (fun index => (measurable_pi_apply index).fst)
  have second_measurable : Measurable
      (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) :=
    measurable_pi_lambda _ (fun index => (measurable_pi_apply index).snd)
  have pair_measurable : Measurable
      (fun bits : (ℕ × Bool) → Bool => fun index => (bits (index, false), bits (index, true))) :=
    measurable_pi_lambda _ (fun index =>
      (measurable_pi_apply (index, false)).prodMk (measurable_pi_apply (index, true)))
  apply (indepFun_iff_map_prod_eq_prod_map_map
    first_measurable.aemeasurable second_measurable.aemeasurable).mpr
  rw [← flat_bits_paired_address_law]
  rw [Measure.map_map (first_measurable.prodMk second_measurable) pair_measurable,
    Measure.map_map first_measurable pair_measurable,
    Measure.map_map second_measurable pair_measurable]
  exact streams.map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun index => measurable_pi_apply (index, false))).aemeasurable
    (measurable_pi_lambda _ (fun index => measurable_pi_apply (index, true))).aemeasurable

theorem paired_address_first_stream_law :
    First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) =
      addressProbability := by
  have mapped := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => (PMF.uniformOfFintype (Bool × Bool)).toMeasure)
    (f := fun _ pair => pair.1) (by fun_prop)
  simpa only [First.Roots.pairedAddressMeasure, fair_paired_digit_product,
    Measure.map_fst_prod, measure_univ, one_smul, addressProbability] using mapped

theorem paired_address_second_stream_law :
    First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) =
      addressProbability := by
  have mapped := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => (PMF.uniformOfFintype (Bool × Bool)).toMeasure)
    (f := fun _ pair => pair.2) (by fun_prop)
  simpa only [First.Roots.pairedAddressMeasure, fair_paired_digit_product,
    Measure.map_snd_prod, measure_univ, one_smul, addressProbability] using mapped

theorem paired_address_streams_product_law :
    First.Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
      ((fun index => (digits index).1), (fun index => (digits index).2))) =
      addressProbability.prod addressProbability := by
  rw [paired_address_streams_independent.map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun index => (measurable_pi_apply index).fst)).aemeasurable
    (measurable_pi_lambda _ (fun index => (measurable_pi_apply index).snd)).aemeasurable,
    paired_address_first_stream_law, paired_address_second_stream_law]

end LambdaCantor.AE
