import LambdaCantor.First.LinearRegularityRectangle
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
namespace LambdaCantor.First.LinearRegularity

/-- Countable rational rectangles exhaust the full supercritical contraction
range. Every stated density and Fourier energy concerns the actual projected
law; no manuscript regularity conclusion is assumed. -/
theorem projected_law_positive_sobolev_off_exception :
    ∃ exceptional : Set (ℝ × ℝ), dimH exceptional ≤ 1 ∧
      ∀ ratio ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2), ∀ slope : ℝ,
        (ratio, slope) ∉ exceptional →
        HasPositiveSobolevDensity (Roots.pairedAddressMeasure.map (pairedProjection ratio slope)) := by
  let Rectangles := {bounds : (ℚ × ℚ) × (ℚ × ℚ) //
    (1 / 4 : ℝ) < (bounds.1.1 : ℝ) ∧
      (bounds.1.1 : ℝ) < (bounds.1.2 : ℝ) ∧
      (bounds.1.2 : ℝ) < 1 / 2 ∧ (bounds.2.1 : ℝ) < (bounds.2.2 : ℝ)}
  have hlocal (rectangle : Rectangles) :
      ∃ exceptional : Set (ℝ × ℝ), dimH exceptional ≤ 1 ∧
        ∀ parameter ∈ Set.Ioo (rectangle.val.1.1 : ℝ) (rectangle.val.1.2 : ℝ) ×ˢ
            Set.Ioo (rectangle.val.2.1 : ℝ) (rectangle.val.2.2 : ℝ),
          parameter ∉ exceptional →
          HasPositiveSobolevDensity (Roots.pairedAddressMeasure.map (pairedProjection parameter.1 parameter.2)) :=
    projected_law_regular_rectangle rectangle.property.1 rectangle.property.2.1
      rectangle.property.2.2.1 rectangle.property.2.2.2
  choose exceptional hdimension hregular using hlocal
  refine ⟨⋃ rectangle : Rectangles, exceptional rectangle, ?_, ?_⟩
  · rw [dimH_iUnion]
    exact iSup_le hdimension
  intro ratio hratio slope houtside
  obtain ⟨lower, hlower⟩ := exists_rat_btwn hratio.1
  obtain ⟨upper, hupper⟩ := exists_rat_btwn hratio.2
  obtain ⟨lowerSlope, hlowerSlope⟩ := exists_rat_btwn (show slope - 1 < slope by linarith)
  obtain ⟨upperSlope, hupperSlope⟩ := exists_rat_btwn (show slope < slope + 1 by linarith)
  let rectangle : Rectangles := ⟨((lower, upper), (lowerSlope, upperSlope)),
    hlower.1, hlower.2.trans hupper.1, hupper.2, hlowerSlope.2.trans hupperSlope.1⟩
  apply hregular rectangle (ratio, slope)
    ⟨⟨hlower.2, hupper.1⟩, ⟨hlowerSlope.2, hupperSlope.1⟩⟩
  intro h
  exact houtside (Set.mem_iUnion.mpr ⟨rectangle, h⟩)

/-- The manuscript's positive-slope formulation. The exceptional set lies
inside the stated parameter domain, and the measure is the actual law of
the two independent fair Cantor coordinates. -/
theorem linear_regularity :
    ∃ exceptional : Set (ℝ × ℝ),
      exceptional ⊆ Set.Ioo (1 / 4 : ℝ) (1 / 2) ×ˢ Set.Ioi (0 : ℝ) ∧
      dimH exceptional ≤ 1 ∧
      ∀ ratio ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2), ∀ slope ∈ Set.Ioi (0 : ℝ),
        (ratio, slope) ∉ exceptional →
        HasPositiveSobolevDensity
          (Roots.pairedAddressMeasure.map (pairedProjection ratio slope)) := by
  obtain ⟨exceptional, hdimension, hregular⟩ :=
    projected_law_positive_sobolev_off_exception
  refine ⟨exceptional ∩ (Set.Ioo (1 / 4 : ℝ) (1 / 2) ×ˢ Set.Ioi (0 : ℝ)),
    Set.inter_subset_right, (dimH_mono Set.inter_subset_left).trans hdimension, ?_⟩
  intro ratio hratio slope hslope houtside
  apply hregular ratio hratio slope
  intro hmember
  exact houtside ⟨hmember, hratio, hslope⟩

end LambdaCantor.First.LinearRegularity

#print axioms LambdaCantor.First.LinearRegularity.projected_law_positive_sobolev_off_exception
#print axioms LambdaCantor.First.LinearRegularity.linear_regularity

