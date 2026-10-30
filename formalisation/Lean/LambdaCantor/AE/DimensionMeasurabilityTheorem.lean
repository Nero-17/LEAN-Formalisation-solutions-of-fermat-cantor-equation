import LambdaCantor.AE.DimensionMeasurabilityConverse
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace LambdaCantor.AE

theorem measurableSet_hausdorffMeasure_zero_band {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper)
    {dimension : ℝ} (dimension_positive : 0 < dimension) :
    MeasurableSet {ratio : Set.Icc lower upper |
      Measure.hausdorffMeasure dimension (intersection exponent ratio.val) = 0} := by
  have test_measurable := measurableSet_finiteOpenCoverTest exponent_positive lower_nonnegative
    upper_lt_one ordered dimension (fun index => (((1 : ℝ≥0)/(index+1) : ℝ≥0) : ℝ≥0∞))
  convert test_measurable using 1
  ext ratio
  constructor
  · intro zero_measure precision
    exact exists_finiteOpenCover_of_hausdorffMeasure_zero
      (isCompact_intersection exponent_positive (lower_nonnegative.trans ratio.property.1)
        (ratio.property.2.trans_lt upper_lt_one)) dimension_positive zero_measure _ (by positivity)
  · intro test
    apply hausdorffMeasure_zero_of_finiteOpenCoverTest _ test
    exact ENNReal.continuous_coe.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun index : ℕ => (1 : ℝ≥0)/(index+1)) atTop (𝓝 0))

/-- Positive rational exponents suffice, including when the fibre has dimension zero. -/
theorem dimH_lt_iff_exists_positive_rational_null (fibre : Set (ℝ × ℝ)) (bound : ℝ≥0∞) :
    dimH fibre < bound ↔ ∃ dimension : ℚ, 0 < dimension ∧
      ENNReal.ofReal (dimension : ℝ) < bound ∧
      Measure.hausdorffMeasure (dimension : ℝ) fibre = 0 := by
  constructor
  · intro below
    obtain ⟨dimension, nonnegative, above_dim, below_bound⟩ :=
      ENNReal.lt_iff_exists_rat_btwn.mp below
    have positive : 0 < (dimension : ℝ) := by
      have positive_coe : (0 : ℝ≥0∞) < (Real.toNNReal (dimension : ℝ) : ℝ≥0∞) :=
        lt_of_le_of_lt bot_le above_dim
      exact Real.toNNReal_pos.mp (ENNReal.coe_pos.mp positive_coe)
    refine ⟨dimension, by exact_mod_cast positive, below_bound, ?_⟩
    have zero_measure := hausdorffMeasure_of_dimH_lt above_dim
    simpa only [Real.coe_toNNReal _ positive.le] using zero_measure
  · rintro ⟨dimension, positive, below_bound, zero_measure⟩
    have positive_real : 0 < (dimension : ℝ) := by exact_mod_cast positive
    have zero_measure' : Measure.hausdorffMeasure (Real.toNNReal (dimension : ℝ)) fibre = 0 := by
      simpa only [Real.coe_toNNReal _ positive_real.le] using zero_measure
    exact (dimH_le_of_hausdorffMeasure_ne_top
      (zero_measure'.trans_ne ENNReal.zero_ne_top)).trans_lt below_bound

theorem measurable_dimH_intersection_band {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper) :
    Measurable (fun ratio : Set.Icc lower upper => dimH (intersection exponent ratio.val)) := by
  apply measurable_of_Iio
  intro bound
  simp only [preimage_setOf_eq, Iio, dimH_lt_iff_exists_positive_rational_null,
    setOf_exists, setOf_and]
  apply MeasurableSet.iUnion
  intro dimension
  by_cases positive : 0 < dimension
  · simp only [positive, true_and, setOf_true, univ_inter]
    apply MeasurableSet.inter
    · by_cases below : ENNReal.ofReal (dimension : ℝ) < bound <;> simp [below]
    · exact measurableSet_hausdorffMeasure_zero_band exponent_positive lower_nonnegative upper_lt_one
        ordered (by exact_mod_cast positive)
  · simp [positive]

/-- The actual dimension-equality parameter set is Borel on each compact band.
No root-fibre or almost-everywhere dimension theorem is used here. -/
theorem measurableSet_dimension_equality_band {exponent lower upper : ℝ}
    (exponent_positive : 0 < exponent) (lower_nonnegative : 0 ≤ lower)
    (upper_lt_one : upper < 1) (ordered : lower ≤ upper) :
    MeasurableSet {ratio : Set.Icc lower upper |
      dimH (intersection exponent ratio.val) = ENNReal.ofReal (expectedDimension ratio.val)} := by
  apply measurableSet_eq_fun (measurable_dimH_intersection_band exponent_positive lower_nonnegative
    upper_lt_one ordered)
  apply Measurable.ennreal_ofReal
  unfold expectedDimension
  fun_prop

end LambdaCantor.AE
