import LambdaCantor.First.LinearRegularityInvariant

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace LambdaCantor.First.LinearRegularity

/-- The actual four-symbol uniform distribution factors into fair bits. -/
theorem fair_pair_product : (PMF.uniformOfFintype (Bool × Bool)).toMeasure =
    (PMF.uniformOfFintype Bool).toMeasure.prod (PMF.uniformOfFintype Bool).toMeasure := by
  apply Measure.ext_of_singleton
  intro pair
  have hsingleton : ({pair} : Set (Bool × Bool)) = ({pair.1} : Set Bool) ×ˢ ({pair.2} : Set Bool) := by
    ext point
    simp only [Set.mem_singleton_iff, Set.mem_prod, Prod.ext_iff]
  rw [hsingleton, Measure.prod_prod]
  rw [← hsingleton]
  simp [PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_prod]
  rw [← ENNReal.mul_inv (a := (2 : ℝ≥0∞)) (b := 2)
    (Or.inl (by norm_num)) (Or.inr (by norm_num))]
  norm_num

/-- Flattened independent fair bits regroup to exactly the paired address law. -/
theorem flat_bits_pair_law :
    (Measure.infinitePi (fun _ : ℕ × Bool => (PMF.uniformOfFintype Bool).toMeasure)).map
      (fun bits index => (bits (index, false), bits (index, true))) = Roots.pairedAddressMeasure := by
  have hpair := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => (PMF.uniformOfFintype Bool).toMeasure) (by decide : false ≠ true)
  have hcurried := Measure.infinitePi_map_curry
    (fun (_ : ℕ) (_ : Bool) => (PMF.uniformOfFintype Bool).toMeasure)
  have hmap := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => Measure.infinitePi (fun _ : Bool => (PMF.uniformOfFintype Bool).toMeasure))
    (f := fun _ bits => (bits false, bits true)) (by fun_prop)
  rw [hpair, ← fair_pair_product] at hmap
  rw [← hcurried, Measure.map_map (by fun_prop) (by fun_prop)] at hmap
  exact hmap

/-- Coordinate stream independence holds internally for the original paired
law, including slopes where projected sparse symbols collide. -/
theorem paired_coordinate_streams_independent :
    IndepFun (fun digits : ℕ → Bool × Bool => fun index => (digits index).1)
      (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) Roots.pairedAddressMeasure := by
  let flat : Measure ((ℕ × Bool) → Bool) :=
    Measure.infinitePi (fun _ : ℕ × Bool => (PMF.uniformOfFintype Bool).toMeasure)
  have hindependent : iIndepFun (fun position (bits : (ℕ × Bool) → Bool) => bits position) flat :=
    iIndepFun_infinitePi (X := fun _ bit => bit) (by fun_prop)
  have hsplit := indep_iSup_of_disjoint
    (fun position : ℕ × Bool => (measurable_pi_apply position).comap_le) hindependent
    (S := {position | position.2 = false}) (T := {position | position.2 = true})
    (by simp [Set.disjoint_left])
  have hstreams : IndepFun (fun bits : (ℕ × Bool) → Bool => fun index => bits (index, false))
      (fun bits : (ℕ × Bool) → Bool => fun index => bits (index, true)) flat := by
    change Indep _ _ flat
    apply indep_of_indep_of_le hsplit
    · rw [MeasurableSpace.comap_process_pi]
      exact iSup_le fun index => le_iSup_of_le (index, false) (le_iSup_of_le rfl le_rfl)
    · rw [MeasurableSpace.comap_process_pi]
      exact iSup_le fun index => le_iSup_of_le (index, true) (le_iSup_of_le rfl le_rfl)
  have hfirst : Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) :=
    measurable_pi_lambda _ (fun index => measurable_fst.comp (measurable_pi_apply index))
  have hsecond : Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) :=
    measurable_pi_lambda _ (fun index => measurable_snd.comp (measurable_pi_apply index))
  have hpair : Measurable (fun bits : (ℕ × Bool) → Bool =>
      fun index => (bits (index, false), bits (index, true))) :=
    measurable_pi_lambda _ (fun index =>
      (measurable_pi_apply (index, false)).prodMk (measurable_pi_apply (index, true)))
  have hfalse : Measurable (fun bits : (ℕ × Bool) → Bool => fun index => bits (index, false)) :=
    measurable_pi_lambda _ (fun index => measurable_pi_apply (index, false))
  have htrue : Measurable (fun bits : (ℕ × Bool) → Bool => fun index => bits (index, true)) :=
    measurable_pi_lambda _ (fun index => measurable_pi_apply (index, true))
  apply (indepFun_iff_map_prod_eq_prod_map_map hfirst.aemeasurable hsecond.aemeasurable).mpr
  rw [← flat_bits_pair_law]
  rw [Measure.map_map (hfirst.prodMk hsecond) hpair,
    Measure.map_map hfirst hpair, Measure.map_map hsecond hpair]
  exact hstreams.map_prod_eq_prod_map_map hfalse.aemeasurable htrue.aemeasurable

end LambdaCantor.First.LinearRegularity

