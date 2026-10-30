import LambdaCantor.First.LinearRegularityIndependence

noncomputable section
open MeasureTheory ProbabilityTheory
namespace LambdaCantor.First.LinearRegularity

def sparseProjection (ratio slope : ℝ) (blockLength : ℕ) (digits : ℕ → Bool × Bool) : ℝ :=
  slope * address ratio (sparseDigits blockLength (fun index => (digits index).1)) +
    address ratio (sparseDigits blockLength (fun index => (digits index).2))

def denseProjection (ratio slope : ℝ) (blockLength : ℕ) (digits : ℕ → Bool × Bool) : ℝ :=
  slope * address ratio (denseDigits blockLength (fun index => (digits index).1)) +
    address ratio (denseDigits blockLength (fun index => (digits index).2))

theorem measurable_sparseDigits (blockLength : ℕ) : Measurable (sparseDigits blockLength) := by
  apply measurable_pi_lambda
  intro index
  unfold sparseDigits
  split_ifs <;> fun_prop

theorem measurable_denseDigits (blockLength : ℕ) : Measurable (denseDigits blockLength) := by
  apply measurable_pi_lambda
  intro index
  unfold denseDigits
  split_ifs <;> fun_prop

theorem measurable_sparseProjection {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (slope : ℝ) (blockLength : ℕ) : Measurable (sparseProjection ratio slope blockLength) := by
  have haddress := (continuous_address hpos hlt).measurable
  have hleft : Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) := by fun_prop
  have hright : Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) := by fun_prop
  exact ((haddress.comp ((measurable_sparseDigits blockLength).comp hleft)).const_mul slope).add
    (haddress.comp ((measurable_sparseDigits blockLength).comp hright))

theorem measurable_denseProjection {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (slope : ℝ) (blockLength : ℕ) : Measurable (denseProjection ratio slope blockLength) := by
  have haddress := (continuous_address hpos hlt).measurable
  have hleft : Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) := by fun_prop
  have hright : Measurable (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) := by fun_prop
  exact ((haddress.comp ((measurable_denseDigits blockLength).comp hleft)).const_mul slope).add
    (haddress.comp ((measurable_denseDigits blockLength).comp hright))

/-- The projected Cantor law is the convolution of its actual sparse and
dense digit factors. Both laws live on the original fair paired address space. -/
theorem pairedProjection_law_convolution {ratio : ℝ} (hpos : 0 ≤ ratio) (hlt : ratio < 1)
    (slope : ℝ) (blockLength : ℕ) :
    Roots.pairedAddressMeasure.map (pairedProjection ratio slope) =
      (Roots.pairedAddressMeasure.map (sparseProjection ratio slope blockLength)) ∗
        (Roots.pairedAddressMeasure.map (denseProjection ratio slope blockLength)) := by
  have hequal : pairedProjection ratio slope =
      sparseProjection ratio slope blockLength + denseProjection ratio slope blockLength := by
    funext digits
    exact paired_projection_digit_split hpos hlt slope blockLength
      (fun index => (digits index).1) (fun index => (digits index).2)
  rw [hequal]
  exact (sparse_dense_projections_independent hpos hlt slope blockLength).map_add_eq_map_conv_map
    (measurable_sparseProjection hpos hlt slope blockLength)
    (measurable_denseProjection hpos hlt slope blockLength)

end LambdaCantor.First.LinearRegularity
