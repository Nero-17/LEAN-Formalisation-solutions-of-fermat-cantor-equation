import LambdaCantor.First.LinearRegularitySparseLaw

noncomputable section
open MeasureTheory ProbabilityTheory
namespace LambdaCantor.First.LinearRegularity

/-- Convolution with an arbitrary probability measure preserves power
Fourier decay, with the same constants. -/
theorem HasPowerFourierDecay.conv_left {left right : Measure ℝ}
    [IsProbabilityMeasure left] [IsProbabilityMeasure right]
    (hdecay : HasPowerFourierDecay right) : HasPowerFourierDecay (left ∗ right) := by
  obtain ⟨order, constant, horder, hconstant, hbound⟩ := hdecay
  refine ⟨order, constant, horder, hconstant, ?_⟩
  intro frequency hfrequency
  rw [charFun_conv, norm_mul]
  calc
    _ ≤ 1 * ‖charFun right frequency‖ :=
      mul_le_mul_of_nonneg_right (norm_charFun_le_one frequency) (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hbound frequency hfrequency

/-- Sparse Y decay passes to the genuine paired sparse factor at every
real slope, including all coincident-symbol slopes. -/
theorem sparseProjection_fourier_of_coordinate {ratio : ℝ}
    (hpositive : 0 ≤ ratio) (hlt : ratio < 1) (slope : ℝ) (blockLength : ℕ)
    (hdecay : HasPowerFourierDecay ((uniformSymbolMeasure (Alphabet := Bool)).map
      (fun digits => address ratio (sparseDigits blockLength digits)))) :
    HasPowerFourierDecay (Roots.pairedAddressMeasure.map (sparseProjection ratio slope blockLength)) := by
  have hcoordinate : Measurable (fun digits : ℕ → Bool => address ratio (sparseDigits blockLength digits)) :=
    (continuous_address hpositive hlt).measurable.comp (measurable_sparseDigits blockLength)
  have hindependent := paired_coordinate_streams_independent.comp
    (hcoordinate.const_mul slope) hcoordinate
  have hleft : Measurable (fun digits : ℕ → Bool × Bool =>
      slope * address ratio (sparseDigits blockLength (fun index => (digits index).1))) := by
    exact (hcoordinate.comp (by fun_prop)).const_mul slope
  have hright : Measurable (fun digits : ℕ → Bool × Bool =>
      address ratio (sparseDigits blockLength (fun index => (digits index).2))) := by
    exact hcoordinate.comp (by fun_prop)
  have hrightLaw : Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
      address ratio (sparseDigits blockLength (fun index => (digits index).2))) =
      (uniformSymbolMeasure (Alphabet := Bool)).map
        (fun digits => address ratio (sparseDigits blockLength digits)) := by
    rw [← paired_second_stream_law, Measure.map_map hcoordinate (by fun_prop)]
    rfl
  have hconvolution := hindependent.map_add_eq_map_conv_map hleft hright
  have hsum : ((fun digits : ℕ → Bool × Bool =>
      slope * address ratio (sparseDigits blockLength (fun index => (digits index).1))) +
      (fun digits : ℕ → Bool × Bool =>
        address ratio (sparseDigits blockLength (fun index => (digits index).2)))) =
      sparseProjection ratio slope blockLength := by
    funext digits
    rfl
  have hidentity : Roots.pairedAddressMeasure.map (sparseProjection ratio slope blockLength) =
      (Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
        slope * address ratio (sparseDigits blockLength (fun index => (digits index).1)))) ∗
      ((uniformSymbolMeasure (Alphabet := Bool)).map
        (fun digits => address ratio (sparseDigits blockLength digits))) := by
    simpa only [Function.comp_def, hsum, hrightLaw] using hconvolution
  rw [hidentity]
  letI : IsProbabilityMeasure (Roots.pairedAddressMeasure.map (fun digits : ℕ → Bool × Bool =>
      slope * address ratio (sparseDigits blockLength (fun index => (digits index).1)))) :=
    Measure.isProbabilityMeasure_map hleft.aemeasurable
  letI : IsProbabilityMeasure ((uniformSymbolMeasure (Alphabet := Bool)).map
      (fun digits => address ratio (sparseDigits blockLength digits))) :=
    Measure.isProbabilityMeasure_map hcoordinate.aemeasurable
  exact hdecay.conv_left

theorem sparseProjection_generic_fourier :
    ∃ exceptional : Set ℝ, dimH exceptional = 0 ∧
      ∀ (ratio slope : ℝ) (blockLength : ℕ), 0 < ratio → ratio < 1 → 0 < blockLength →
        ratio ^ blockLength ∉ exceptional →
        HasPowerFourierDecay (Roots.pairedAddressMeasure.map (sparseProjection ratio slope blockLength)) := by
  obtain ⟨exceptional, hdimension, hfourier⟩ := sparse_coordinate_generic_fourier
  exact ⟨exceptional, hdimension, fun ratio slope blockLength hpositive hlt hblock houtside =>
    sparseProjection_fourier_of_coordinate hpositive.le hlt slope blockLength
      (hfourier ratio blockLength hpositive hlt hblock houtside)⟩

end LambdaCantor.First.LinearRegularity
