import LambdaCantor.First.RootsL1Limit
import LambdaCantor.First.RootsConditionalBase

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace LambdaCantor.First.Roots

/-- Actual density of a restricted source event under disintegration. The
conditional kernel itself chooses coherent density versions for every event. -/
theorem conditional_event_density {exponent : ℝ} (data : RootFibreData exponent)
    (source : Measure (ℕ → Bool × Bool)) [IsFiniteMeasure source]
    (density : ℝ → ℝ) (nonnegative : ∀ point, 0 ≤ density point)
    (measurable : Measurable density) (integrable : Integrable density volume)
    (law : source.map data.root = volume.withDensity (fun point => ENNReal.ofReal (density point)))
    (event : Set (ℕ → Bool × Bool)) (event_measurable : MeasurableSet event) :
    (∀ point, 0 ≤ density point * (condDistrib id data.root source point event).toReal) ∧
      Measurable (fun point => density point * (condDistrib id data.root source point event).toReal) ∧
      Integrable (fun point => density point * (condDistrib id data.root source point event).toReal) volume ∧
      (source.restrict event).map data.root = volume.withDensity (fun point => ENNReal.ofReal
        (density point * (condDistrib id data.root source point event).toReal)) := by
  have kernel_measurable := Kernel.measurable_coe (condDistrib id data.root source) event_measurable
  have kernel_bound (point : ℝ) : (condDistrib id data.root source point event).toReal ≤ 1 := by
    have comparison : condDistrib id data.root source point event ≤ 1 := by
      simpa using (measure_mono (Set.subset_univ event) :
        condDistrib id data.root source point event ≤ condDistrib id data.root source point Set.univ)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top comparison
  refine ⟨fun point => mul_nonneg (nonnegative point) ENNReal.toReal_nonneg,
    measurable.mul kernel_measurable.ennreal_toReal,
    integrable.mul_bdd kernel_measurable.ennreal_toReal.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun point => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using kernel_bound point)), ?_⟩
  have ennreal_law : (source.restrict event).map data.root =
      volume.withDensity (fun point => ENNReal.ofReal (density point) *
        condDistrib id data.root source point event) := by
    apply Measure.ext
    intro subset subset_measurable
    rw [Measure.map_apply (rootFibreData_continuous_root data).measurable subset_measurable,
      Measure.restrict_apply ((rootFibreData_continuous_root data).measurable subset_measurable),
      withDensity_apply _ subset_measurable]
    have density_integral : (∫⁻ point in subset, condDistrib id data.root source point event
        ∂source.map data.root) =
        ∫⁻ point in subset, ENNReal.ofReal (density point) * condDistrib id data.root source point event := by
      rw [law]
      simpa only [Pi.mul_apply] using
        (setLIntegral_withDensity_eq_lintegral_mul₀ measurable.ennreal_ofReal.aemeasurable
          kernel_measurable.aemeasurable subset_measurable)
    rw [← density_integral,
      setLIntegral_map subset_measurable kernel_measurable (rootFibreData_continuous_root data).measurable,
      setLIntegral_preimage_condDistrib (rootFibreData_continuous_root data).measurable
        aemeasurable_id event_measurable subset_measurable]
    rfl
  rw [ennreal_law]
  congr 1
  funext point
  rw [ENNReal.ofReal_mul (nonnegative point), ENNReal.ofReal_toReal (measure_ne_top _ _)]

def goodSetRootDensity {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) : ℝ → ℝ :=
  Classical.choose (rootSobolevGoodSet_actual_density data orderIndex bound)

theorem goodSetRootDensity_properties {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) :
    (∀ point, 0 ≤ goodSetRootDensity data orderIndex bound point) ∧
      Measurable (goodSetRootDensity data orderIndex bound) ∧
      Integrable (goodSetRootDensity data orderIndex bound) volume ∧
      (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root =
        volume.withDensity (fun point => ENNReal.ofReal (goodSetRootDensity data orderIndex bound point)) :=
  Classical.choose_spec (rootSobolevGoodSet_actual_density data orderIndex bound)

def goodSetRootConditional {exponent : ℝ} (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    Kernel ℝ (ℕ → Bool × Bool) :=
  condDistrib id data.root (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound))

instance goodSetRootConditional_markov {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) : IsMarkovKernel (goodSetRootConditional data orderIndex bound) := by
  unfold goodSetRootConditional
  infer_instance

/-- Finite-word cylinders keep the simultaneous exceptional set countable. -/
def finitePairedPrefix {depth : ℕ} (word : Fin depth → Bool × Bool) : Set (ℕ → Bool × Bool) :=
  {digits | ∀ index : Fin depth, digits index = word index}

theorem measurableSet_finitePairedPrefix {depth : ℕ} (word : Fin depth → Bool × Bool) :
    MeasurableSet (finitePairedPrefix word) := by
  have equality : finitePairedPrefix word =
      (fun digits : ℕ → Bool × Bool => fun index : Fin depth => digits index) ⁻¹' {word} := by
    ext digits
    simp only [finitePairedPrefix, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
  rw [equality]
  exact (measurableSet_singleton word).preimage (by fun_prop)

theorem finitePairedPrefix_eq_pairedPrefix (digits : ℕ → Bool × Bool) (depth : ℕ) :
    finitePairedPrefix (fun index : Fin depth => digits index) = pairedPrefix digits depth := by
  ext other
  constructor
  · intro equality index before
    exact equality ⟨index, before⟩
  · intro equality index
    exact equality index index.isLt

def goodSetPrefixDensity {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool) (point : ℝ) : ℝ :=
  (4 : ℝ) ^ depth * (goodSetRootDensity data orderIndex bound point *
    (goodSetRootConditional data orderIndex bound point (finitePairedPrefix word)).toReal)

theorem goodSetPrefixDensity_properties {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool) :
    (∀ point, 0 ≤ goodSetPrefixDensity data orderIndex bound depth word point) ∧
      Measurable (goodSetPrefixDensity data orderIndex bound depth word) ∧
      Integrable (goodSetPrefixDensity data orderIndex bound depth word) volume := by
  have properties := goodSetRootDensity_properties data orderIndex bound
  have event_properties := conditional_event_density data
    (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound))
    _ properties.1 properties.2.1 properties.2.2.1 properties.2.2.2
    (finitePairedPrefix word) (measurableSet_finitePairedPrefix word)
  refine ⟨fun point => mul_nonneg (by positivity) (event_properties.1 point),
    measurable_const.mul event_properties.2.1, event_properties.2.2.1.const_mul _⟩

/-- The canonical conditional prefix density is the actual scaled restricted
root law. Fresh kernels and conditional tails are never identified by fiat. -/
theorem goodSetPrefixDensity_law {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool) :
    ((4 : ℝ≥0∞) ^ depth) •
      ((pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).restrict
        (finitePairedPrefix word)).map data.root =
      volume.withDensity (fun point => ENNReal.ofReal (goodSetPrefixDensity data orderIndex bound depth word point)) := by
  have properties := goodSetRootDensity_properties data orderIndex bound
  have event_properties := conditional_event_density data
    (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound))
    _ properties.1 properties.2.1 properties.2.2.1 properties.2.2.2
    (finitePairedPrefix word) (measurableSet_finitePairedPrefix word)
  rw [event_properties.2.2.2, ← withDensity_smul _ event_properties.2.1.ennreal_ofReal]
  congr 1
  funext point
  simp only [goodSetPrefixDensity, goodSetRootConditional, Pi.smul_apply, smul_eq_mul,
    ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ) ^ depth),
    ENNReal.ofReal_pow (by norm_num : 0 ≤ (4 : ℝ)), ENNReal.ofReal_ofNat]

/-- Exact conditional prefix mass at every point where the chosen root density
is positive; finiteness follows from the probability kernel. -/
theorem goodSetConditional_prefix_mass {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound depth : ℕ) (word : Fin depth → Bool × Bool) (point : ℝ)
    (positive : 0 < goodSetRootDensity data orderIndex bound point) :
    goodSetRootConditional data orderIndex bound point (finitePairedPrefix word) =
      ENNReal.ofReal ((4 : ℝ)⁻¹ ^ depth * goodSetPrefixDensity data orderIndex bound depth word point /
        goodSetRootDensity data orderIndex bound point) := by
  have identity : (4 : ℝ)⁻¹ ^ depth * goodSetPrefixDensity data orderIndex bound depth word point /
      goodSetRootDensity data orderIndex bound point =
      (goodSetRootConditional data orderIndex bound point (finitePairedPrefix word)).toReal := by
    have inverse_cancellation : (4 : ℝ)⁻¹ ^ depth * 4 ^ depth = 1 := by
      rw [← mul_pow]
      norm_num
    unfold goodSetPrefixDensity
    calc
      _ = ((4 : ℝ)⁻¹ ^ depth * 4 ^ depth) *
          (goodSetRootDensity data orderIndex bound point *
            (goodSetRootConditional data orderIndex bound point (finitePairedPrefix word)).toReal) /
          goodSetRootDensity data orderIndex bound point := by ring
      _ = _ := by rw [inverse_cancellation, one_mul]; field_simp [positive.ne']
  rw [identity, ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem goodSetRootDensity_ae_positive {exponent : ℝ} (data : RootFibreData exponent)
    (orderIndex bound : ℕ) :
    ∀ᵐ point ∂(pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root,
      0 < goodSetRootDensity data orderIndex bound point := by
  have properties := goodSetRootDensity_properties data orderIndex bound
  rw [properties.2.2.2]
  apply (ae_withDensity_iff properties.2.1.ennreal_ofReal).mpr
  exact Filter.Eventually.of_forall (fun point nonzero => ENNReal.ofReal_ne_zero_iff.mp nonzero)

/-- The compact-source conditional probability lives on the selected compact
set and on its actual root fibre. -/
theorem goodSetRootConditional_ae_selected_fibre {exponent : ℝ}
    (data : RootFibreData exponent) (orderIndex bound : ℕ) :
    ∀ᵐ parameter ∂(pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root,
      ∀ᵐ digits ∂goodSetRootConditional data orderIndex bound parameter,
        digits ∈ rootSobolevGoodSet data orderIndex bound ∧ data.root digits = parameter := by
  apply Measure.ae_ae_of_ae_compProd
    (μ := (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)).map data.root)
    (κ := goodSetRootConditional data orderIndex bound)
    (p := fun pair : ℝ × (ℕ → Bool × Bool) =>
      pair.2 ∈ rootSobolevGoodSet data orderIndex bound ∧ data.root pair.2 = pair.1)
  rw [show goodSetRootConditional data orderIndex bound =
    condDistrib id data.root (pairedAddressMeasure.restrict (rootSobolevGoodSet data orderIndex bound)) from rfl,
    compProd_map_condDistrib aemeasurable_id]
  apply (ae_map_iff
    ((rootFibreData_continuous_root data).measurable.prodMk measurable_id).aemeasurable
    (((rootFibreData_compact_good_set data orderIndex bound).measurableSet.preimage measurable_snd).inter
      (measurableSet_eq_fun ((rootFibreData_continuous_root data).measurable.comp measurable_snd)
        measurable_fst))).mpr
  filter_upwards [ae_restrict_mem (rootFibreData_compact_good_set data orderIndex bound).measurableSet]
    with digits member
  exact ⟨member, rfl⟩

end LambdaCantor.First.Roots
