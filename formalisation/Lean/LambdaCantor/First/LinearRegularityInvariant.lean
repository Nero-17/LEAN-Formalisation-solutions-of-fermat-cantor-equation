import LambdaCantor.First.LinearRegularityBlockSeries
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace LambdaCantor.First.LinearRegularity

variable {Alphabet : Type*} [Fintype Alphabet] [Nonempty Alphabet]
  [MeasurableSpace Alphabet] [MeasurableSingletonClass Alphabet]

def uniformSymbolMeasure : Measure (ℕ → Alphabet) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype Alphabet).toMeasure)

instance uniformSymbolMeasure_probability : IsProbabilityMeasure (uniformSymbolMeasure (Alphabet := Alphabet)) := by
  unfold uniformSymbolMeasure
  infer_instance

def affineAddress (contraction : ℝ) (translation : Alphabet → ℝ) (symbols : ℕ → Alphabet) : ℝ :=
  ∑' index : ℕ, contraction ^ index * translation (symbols index)

theorem affineAddress_summable {contraction : ℝ} (hpositive : 0 ≤ contraction) (hlt : contraction < 1)
    (translation : Alphabet → ℝ) (symbols : ℕ → Alphabet) :
    Summable (fun index : ℕ => contraction ^ index * translation (symbols index)) := by
  obtain ⟨bound, hbound⟩ := (Set.finite_range (fun symbol => ‖translation symbol‖)).bddAbove
  apply ((summable_geometric_of_lt_one hpositive hlt).mul_right bound).of_norm_bounded
  intro index
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hpositive _)]
  exact mul_le_mul_of_nonneg_left (hbound (Set.mem_range_self (symbols index))) (pow_nonneg hpositive _)

theorem measurable_affineAddress (contraction : ℝ) (translation : Alphabet → ℝ) :
    Measurable (affineAddress contraction translation) := by
  apply Measurable.tsum
  intro index
  exact measurable_const.mul ((measurable_of_finite translation).comp (measurable_pi_apply index))

theorem affineAddress_first_symbol {contraction : ℝ} (hpositive : 0 ≤ contraction) (hlt : contraction < 1)
    (translation : Alphabet → ℝ) (symbols : ℕ → Alphabet) :
    affineAddress contraction translation symbols =
      contraction * affineAddress contraction translation (fun index => symbols (index + 1)) +
        translation (symbols 0) := by
  unfold affineAddress
  rw [(affineAddress_summable hpositive hlt translation symbols).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, pow_succ]
  have htail : (∑' index : ℕ, contraction ^ index * contraction * translation (symbols (index + 1))) =
      contraction * ∑' index : ℕ, contraction ^ index * translation (symbols (index + 1)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro index
    ring
  rw [htail]
  ring

theorem uniform_head_tail_independent :
    IndepFun (fun symbols : ℕ → Alphabet => symbols 0)
      (fun symbols : ℕ → Alphabet => fun index : ℕ => symbols (index + 1)) uniformSymbolMeasure := by
  have hindependent : iIndepFun (fun index (symbols : ℕ → Alphabet) => symbols index)
      uniformSymbolMeasure := iIndepFun_infinitePi (X := fun _ symbol => symbol) (by fun_prop)
  have hsplit := indep_iSup_of_disjoint
    (fun index : ℕ => (measurable_pi_apply index).comap_le) hindependent
    (S := ({0} : Set ℕ)) (T := Set.range Nat.succ) (by simp [Set.disjoint_left])
  change Indep (MeasurableSpace.comap (fun symbols : ℕ → Alphabet => symbols 0) inferInstance)
    (MeasurableSpace.comap (fun symbols : ℕ → Alphabet => fun index : ℕ => symbols (index + 1)) inferInstance)
    uniformSymbolMeasure
  apply indep_of_indep_of_le hsplit
  · exact le_iSup_of_le 0 (le_iSup_of_le (Set.mem_singleton 0) le_rfl)
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le fun index => le_iSup_of_le (index + 1) (le_iSup_of_le ⟨index, rfl⟩ le_rfl)

theorem uniform_head_tail_law :
    uniformSymbolMeasure.map
      (fun symbols : ℕ → Alphabet => (symbols 0, fun index : ℕ => symbols (index + 1))) =
    (PMF.uniformOfFintype Alphabet).toMeasure.prod uniformSymbolMeasure := by
  have hhead : Measurable (fun symbols : ℕ → Alphabet => symbols 0) := measurable_pi_apply 0
  have htail : Measurable (fun symbols : ℕ → Alphabet => fun index => symbols (index + 1)) :=
    measurable_pi_lambda _ (fun index => measurable_pi_apply (index + 1))
  rw [uniform_head_tail_independent.map_prod_eq_prod_map_map hhead.aemeasurable htail.aemeasurable]
  unfold uniformSymbolMeasure
  rw [Measure.infinitePi_map_eval, Measure.map_infinitePi_infinitePi_of_inj Nat.succ_injective]

/-- Actual IID affine-series law satisfies its finite equal-weight invariant
measure equation. This is proved from the product law, not assumed. -/
theorem affineAddress_law_invariant {contraction : ℝ} (hpositive : 0 ≤ contraction) (hlt : contraction < 1)
    (translation : Alphabet → ℝ) :
    uniformSymbolMeasure.map (affineAddress contraction translation) =
      ∑ symbol : Alphabet, (Fintype.card Alphabet : ℝ≥0∞)⁻¹ •
        (uniformSymbolMeasure.map (affineAddress contraction translation)).map
          (fun point : ℝ => contraction * point + translation symbol) := by
  let combine : Alphabet × (ℕ → Alphabet) → ℝ := fun pair =>
    contraction * affineAddress contraction translation pair.2 + translation pair.1
  have hcombine : Measurable combine :=
    (measurable_const.mul ((measurable_affineAddress contraction translation).comp measurable_snd)).add
      ((measurable_of_finite translation).comp measurable_fst)
  have hmap : uniformSymbolMeasure.map (affineAddress contraction translation) =
      ((PMF.uniformOfFintype Alphabet).toMeasure.prod uniformSymbolMeasure).map combine := by
    rw [← uniform_head_tail_law, Measure.map_map hcombine (by fun_prop)]
    congr 1
    funext symbols
    exact affineAddress_first_symbol hpositive hlt translation symbols
  have huniform : (PMF.uniformOfFintype Alphabet).toMeasure =
      Measure.sum (fun symbol : Alphabet => (Fintype.card Alphabet : ℝ≥0∞)⁻¹ • Measure.dirac symbol) := by
    calc
      _ = Measure.sum (fun symbol : Alphabet =>
          (PMF.uniformOfFintype Alphabet).toMeasure {symbol} • Measure.dirac symbol) :=
        (Measure.sum_smul_dirac (PMF.uniformOfFintype Alphabet).toMeasure).symm
      _ = _ := by
        congr 1
        funext symbol
        exact congrArg (fun mass : ℝ≥0∞ => mass • Measure.dirac symbol)
          (((PMF.uniformOfFintype Alphabet).toMeasure_apply_singleton symbol
            (measurableSet_singleton _)).trans (PMF.uniformOfFintype_apply symbol))
  conv_lhs => rw [hmap]
  rw [huniform, Measure.prod_sum_left, Measure.map_sum hcombine.aemeasurable]
  simp_rw [Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map hcombine measurable_prodMk_left]
  rw [Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro symbol hsymbol
  congr 1
  rw [Measure.map_map (by fun_prop) (measurable_affineAddress contraction translation)]
  rfl

/-- The genuine dense projected law is invariant under the analytic dense
block IFS, with exactly 4^(M-1) equally weighted symbols. -/
theorem denseProjection_law_invariant {ratio : ℝ} (hpositive : 0 ≤ ratio) (hlt : ratio < 1)
    (slope : ℝ) (blockLength : ℕ) (hblock : 0 < blockLength) :
    Roots.pairedAddressMeasure.map (denseProjection ratio slope blockLength) =
      ∑ word : DenseBlock blockLength, (4 ^ (blockLength - 1) : ℝ≥0∞)⁻¹ •
        (Roots.pairedAddressMeasure.map (denseProjection ratio slope blockLength)).map
          (fun point : ℝ => ratio ^ blockLength * point + denseBlockTranslation blockLength (ratio, slope) word) := by
  have hidentification : Roots.pairedAddressMeasure.map (denseProjection ratio slope blockLength) =
      uniformSymbolMeasure.map (affineAddress (ratio ^ blockLength)
        (denseBlockTranslation blockLength (ratio, slope))) := by
    rw [show uniformSymbolMeasure (Alphabet := DenseBlock blockLength) =
      Roots.pairedAddressMeasure.map (denseBlockCoding blockLength) from (denseBlockCoding_law blockLength).symm]
    rw [Measure.map_map (measurable_affineAddress _ _) (measurable_denseBlockCoding blockLength)]
    congr 1
    funext digits
    exact denseProjection_block_series hpositive hlt slope blockLength hblock digits
  rw [hidentification]
  simpa only [denseBlock_card, Nat.cast_pow, Nat.cast_ofNat] using
    affineAddress_law_invariant (pow_nonneg hpositive blockLength)
      (pow_lt_one₀ hpositive hlt hblock.ne') (denseBlockTranslation blockLength (ratio, slope))

end LambdaCantor.First.LinearRegularity

