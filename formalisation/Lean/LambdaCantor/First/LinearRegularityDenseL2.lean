import LambdaCantor.First.LinearRegularityBlockCollisions
import LambdaCantor.First.LinearRegularityExternal
import Mathlib.Analysis.Convex.Topology

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LambdaCantor.First.LinearRegularity

/-- Actual generic L2 regularity of the retained dense projected law on a
parameter rectangle with strict similarity surplus. -/
theorem denseProjection_generic_l2 {lower upper lowerSlope upperSlope : ℝ}
    (hlower : 0 < lower) (hordered : lower < upper) (hupper : upper < 1 / 2)
    (hslopes : lowerSlope < upperSlope) (blockLength : ℕ) (hblock : 2 ≤ blockLength)
    (hsurplus : 1 < (4 : ℝ) ^ (blockLength - 1) * lower ^ blockLength) :
    ∃ exceptional : Set (ℝ × ℝ), dimH exceptional ≤ 1 ∧
      ∀ parameter ∈ Set.Ioo lower upper ×ˢ Set.Ioo lowerSlope upperSlope,
        parameter ∉ exceptional →
        HasL2Density (Roots.pairedAddressMeasure.map
          (denseProjection parameter.1 parameter.2 blockLength)) := by
  let symbols := Fintype.equivFin (DenseBlock blockLength)
  have hcard : 2 ≤ Fintype.card (DenseBlock blockLength) := by
    rw [denseBlock_card]
    have h := pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℕ))
      (show 1 ≤ blockLength - 1 by omega)
    norm_num at h
    omega
  have hpositive : 0 < blockLength := by omega
  obtain ⟨exceptional, hsubset, hdimension, hregular⟩ := shmerkin2019_theorem92_uniform_l2
    (Fintype.card (DenseBlock blockLength)) hcard
    (Set.Ioo lower upper ×ˢ Set.Ioo lowerSlope upperSlope) (isOpen_Ioo.prod isOpen_Ioo)
    ((convex_Ioo lower upper).prod (convex_Ioo lowerSlope upperSlope)).isPreconnected
    (fun parameter => parameter.1 ^ blockLength)
    (fun parameter symbol => denseBlockTranslation blockLength parameter (symbols.symm symbol))
    (denseBlockContraction_analytic blockLength _)
    (fun symbol => denseBlockTranslation_analytic blockLength (symbols.symm symbol) _)
    (by
      intro parameter hparameter
      exact denseBlockContraction_mem_unit (hlower.trans hparameter.1.1)
        (hparameter.1.2.trans (hupper.trans (by norm_num))) blockLength hpositive)
    (by
      intro left right hne
      have hwords : (fun index => symbols.symm (left index)) ≠
          (fun index => symbols.symm (right index)) := by
        intro hequal
        apply hne
        funext index
        exact symbols.symm.injective (congrFun hequal index)
      obtain ⟨slope, hslope, hdifferent⟩ := denseBlock_series_nondegenerate
        (show 0 < (lower + upper) / 2 by linarith)
        (show (lower + upper) / 2 < 1 / 2 by linarith) hslopes blockLength hpositive _ _ hwords
      refine ⟨((lower + upper) / 2, slope), ⟨⟨by linarith, by linarith⟩, hslope⟩, ?_⟩
      simpa only [affineAddress, mul_comm] using hdifferent)
  let collisions : Set (ℝ × ℝ) := ⋃ pair : {pair : DenseBlock blockLength × DenseBlock blockLength // pair.1 ≠ pair.2},
    {parameter : ℝ × ℝ | parameter.1 ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      denseBlockTranslation blockLength parameter pair.val.1 = denseBlockTranslation blockLength parameter pair.val.2}
  have hcollisions : dimH collisions ≤ 1 := by
    dsimp only [collisions]
    rw [dimH_iUnion]
    apply iSup_le
    intro pair
    exact dimH_denseBlock_collision blockLength hpositive pair.val.1 pair.val.2 pair.property
  refine ⟨exceptional ∪ collisions, ?_, ?_⟩
  · rw [dimH_union]
    exact max_le hdimension hcollisions
  intro parameter hparameter houtside
  have hratio := hlower.trans hparameter.1.1
  have hhalf := hparameter.1.2.trans hupper
  have hlt : parameter.1 < 1 := hhalf.trans (by norm_num)
  have hinjective : Function.Injective
      (fun symbol => denseBlockTranslation blockLength parameter (symbols.symm symbol)) := by
    intro left right hequal
    by_contra hne
    have hwords : symbols.symm left ≠ symbols.symm right := by
      intro h
      exact hne (symbols.symm.injective h)
    apply houtside
    right
    apply Set.mem_iUnion.mpr
    exact ⟨⟨(symbols.symm left, symbols.symm right), hwords⟩, ⟨hratio, hhalf⟩, hequal⟩
  have hmass : (Fintype.card (DenseBlock blockLength) : ℝ)⁻¹ < parameter.1 ^ blockLength := by
    rw [denseBlock_card]
    exact supercritical_block_mass hlower.le hparameter.1.1.le blockLength hsurplus
  have hinvariant : IsUniformSelfSimilar (Fintype.card (DenseBlock blockLength))
      (Roots.pairedAddressMeasure.map (denseProjection parameter.1 parameter.2 blockLength))
      (parameter.1 ^ blockLength)
      (fun symbol => denseBlockTranslation blockLength parameter (symbols.symm symbol)) := by
    unfold IsUniformSelfSimilar
    have h := denseProjection_law_invariant hratio.le hlt parameter.2 blockLength hpositive
    rw [← symbols.symm.sum_comp (fun word : DenseBlock blockLength =>
      (4 ^ (blockLength - 1) : ℝ≥0∞)⁻¹ •
        (Roots.pairedAddressMeasure.map (denseProjection parameter.1 parameter.2 blockLength)).map
          (fun point : ℝ => parameter.1 ^ blockLength * point +
            denseBlockTranslation blockLength parameter word))] at h
    simpa only [denseBlock_card, Nat.cast_pow, Nat.cast_ofNat] using h
  exact hregular parameter hparameter (fun h => houtside (Or.inl h)) hinjective hmass _
    (Measure.isProbabilityMeasure_map (measurable_denseProjection hratio.le hlt parameter.2 blockLength).aemeasurable)
    hinvariant

end LambdaCantor.First.LinearRegularity

