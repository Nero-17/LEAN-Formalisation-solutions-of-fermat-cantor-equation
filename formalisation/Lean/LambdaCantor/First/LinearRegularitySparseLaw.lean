import LambdaCantor.First.LinearRegularityCoordinates
import LambdaCantor.First.LinearRegularitySparse
import LambdaCantor.First.LinearRegularityExternal

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace LambdaCantor.First.LinearRegularity

theorem paired_second_stream_law : Roots.pairedAddressMeasure.map
    (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) =
    uniformSymbolMeasure (Alphabet := Bool) := by
  unfold Roots.pairedAddressMeasure uniformSymbolMeasure
  rw [Measure.infinitePi_map_pi _ (by fun_prop)]
  simp only [fair_pair_product, Measure.map_snd_prod, measure_univ, one_smul]

theorem sparse_coordinate_affine {ratio : ℝ} (hpositive : 0 ≤ ratio) (hlt : ratio < 1)
    (blockLength : ℕ) (hblock : 0 < blockLength) (digits : ℕ → Bool) :
    address ratio (sparseDigits blockLength digits) =
      affineAddress (ratio ^ blockLength) (fun bit : Bool => (1 - ratio) * (if bit then 1 else 0))
        (fun index => digits (blockLength * index)) := by
  rw [sparse_address_rescaling hpositive hlt blockLength hblock digits]
  unfold address affineAddress
  rw [show (1 - ratio) / (1 - ratio ^ blockLength) *
      ((1 - ratio ^ blockLength) * ∑' index : ℕ,
        (if digits (blockLength * index) then (1 : ℝ) else 0) * (ratio ^ blockLength) ^ index) =
      (1 - ratio) * ∑' index : ℕ,
        (if digits (blockLength * index) then (1 : ℝ) else 0) * (ratio ^ blockLength) ^ index by
    field_simp [ne_of_gt (sub_pos.mpr (pow_lt_one₀ hpositive hlt hblock.ne'))]]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro index
  ring

theorem sparse_coordinate_law {ratio : ℝ} (hpositive : 0 ≤ ratio) (hlt : ratio < 1)
    (blockLength : ℕ) (hblock : 0 < blockLength) :
    (uniformSymbolMeasure (Alphabet := Bool)).map
      (fun digits => address ratio (sparseDigits blockLength digits)) =
    uniformSymbolMeasure.map
      (affineAddress (ratio ^ blockLength) (fun bit : Bool => (1 - ratio) * (if bit then 1 else 0))) := by
  have hinjective : Function.Injective (fun index : ℕ => blockLength * index) := by
    intro left right hequal
    exact mul_left_cancel₀ hblock.ne' hequal
  have hsampling := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure) hinjective
  have hsample : (uniformSymbolMeasure (Alphabet := Bool)).map
      (fun digits index => digits (blockLength * index)) = uniformSymbolMeasure := hsampling
  conv_rhs => rw [← hsample, Measure.map_map (measurable_affineAddress _ _) (by fun_prop)]
  congr 1
  funext digits
  exact sparse_coordinate_affine hpositive hlt blockLength hblock digits

/-- The precise two-map external theorem applies to the actual sparse Y
coordinate, without excluding any projected slope. -/
theorem sparse_coordinate_generic_fourier :
    ∃ exceptional : Set ℝ, dimH exceptional = 0 ∧
      ∀ (ratio : ℝ) (blockLength : ℕ), 0 < ratio → ratio < 1 → 0 < blockLength →
        ratio ^ blockLength ∉ exceptional →
        HasPowerFourierDecay ((uniformSymbolMeasure (Alphabet := Bool)).map
          (fun digits => address ratio (sparseDigits blockLength digits))) := by
  obtain ⟨exceptional, hsubset, hdimension, hfourier⟩ := shmerkin2014_proposition23_two_maps
  refine ⟨exceptional, hdimension, ?_⟩
  intro ratio blockLength hpositive hlt hblock houtside
  rw [sparse_coordinate_law hpositive.le hlt blockLength hblock]
  let symbols : Bool ≃ Fin 2 := Fintype.equivFin Bool
  have htranslation : Function.Injective (fun bit : Bool => (1 - ratio) * (if bit then (1 : ℝ) else 0)) := by
    intro left right hequal
    cases left <;> cases right <;> simp_all <;> linarith
  have hinvariant : IsUniformSelfSimilar 2
      (uniformSymbolMeasure.map (affineAddress (ratio ^ blockLength)
        (fun bit : Bool => (1 - ratio) * (if bit then 1 else 0))))
      (ratio ^ blockLength)
      (fun symbol => (1 - ratio) * (if symbols.symm symbol then 1 else 0)) := by
    unfold IsUniformSelfSimilar
    have h := affineAddress_law_invariant (pow_nonneg hpositive.le _)
      (pow_lt_one₀ hpositive.le hlt hblock.ne') (fun bit : Bool => (1 - ratio) * (if bit then 1 else 0))
    rw [← symbols.symm.sum_comp (fun bit : Bool => (Fintype.card Bool : ℝ≥0∞)⁻¹ •
      (uniformSymbolMeasure.map (affineAddress (ratio ^ blockLength)
        (fun bit : Bool => (1 - ratio) * (if bit then 1 else 0)))).map
          (fun point : ℝ => ratio ^ blockLength * point + (1 - ratio) * (if bit then 1 else 0)))] at h
    simpa only [Fintype.card_bool] using h
  exact hfourier (ratio ^ blockLength)
    ⟨pow_pos hpositive _, pow_lt_one₀ hpositive.le hlt hblock.ne'⟩ houtside _
    (htranslation.comp symbols.symm.injective) _
    (Measure.isProbabilityMeasure_map (measurable_affineAddress _ _).aemeasurable) hinvariant

end LambdaCantor.First.LinearRegularity

