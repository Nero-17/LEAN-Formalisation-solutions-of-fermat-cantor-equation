import LambdaCantor.AE.ActualCenteredKernelExistence
import LambdaCantor.AE.CenteredRootFibreAdapter
import LambdaCantor.AE.DimensionEqualityTerminal
import LambdaCantor.AE.ExponentRange
import LambdaCantor.First.RootsMain

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace LambdaCantor.AE

/-- On every admissible short band, the actual centered densities and the
actual First root-fibre theorem discharge all local-kernel hypotheses of
the Lebesgue density contradiction. No root-mass premise is assumed. -/
theorem ae_dimension_equality_on_actual_admissible_band
    {exponent lower upper regularity : ℝ}
    (irrational : Irrational exponent) (exponent_greater_one : 1 < exponent)
    (lower_quarter : 1/4 < lower) (ordered : lower ≤ upper) (upper_half : upper < 1/2)
    (square_less : upper*upper < lower) (regularity_positive : 0 < regularity)
    (range_bound : 2*regularity < 2*Real.log (8/3 : ℝ)/Real.log (upper/lower^3)-1)
    (summability_room : (upper^2/lower)^(2*regularity) <
      upper^(1-Real.log 2/Real.log (1/lower))) :
    ∀ᵐ centre : ℝ, centre ∈ Ioo lower upper →
      dimH (intersection exponent centre) = ENNReal.ofReal (expectedDimension centre) := by
  have lower_positive : 0 < lower := by linarith
  have upper_positive := lower_positive.trans_le ordered
  have upper_less_one : upper < 1 := by linarith
  have exponent_positive : 0 < exponent := by linarith
  have regularity_le_one := ae_regularity_le_one lower_positive ordered upper_half range_bound
  let good := {ratio : ℝ | ratio ∈ Icc lower upper ∧
    dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio)}
  have good_measurable : MeasurableSet good := measurableSet_dimension_equality_closed_band
    exponent_positive lower_positive.le upper_less_one ordered
  apply ae_dimension_equality_of_local_kernel_estimates exponent_positive lower_positive.le upper_less_one ordered
  filter_upwards [ae_irrational_actual_centered_kernel_limits irrational exponent_greater_one lower_positive ordered upper_half
    square_less regularity_positive regularity_le_one range_bound summability_room] with centre kernels
  intro centre_inside
  have centre_positive := lower_positive.trans centre_inside.1
  have centre_less_one := centre_inside.2.trans upper_less_one
  obtain ⟨horizontalDepth, verticalDepth, width, slope, averageConstant, errorConstant, initialL2Constant,
    width_positive, slope_positive, average_positive, error_nonnegative, initialL2_positive, kernels⟩ := kernels centre_inside
  have window_inside := centered_window_eventually_mem_nhds (windowConstant := width)
    centre_positive centre_less_one (Ioo_mem_nhds centre_inside.1 centre_inside.2)
  have vanishing := freezing_total_error_tendsto_zero 1 centre_positive centre_less_one lower_positive
    upper_positive regularity_positive summability_room
  have total_error_zero : Tendsto (fun index : ℕ => errorConstant*(centre^index)^(regularity/(1+regularity))*
      ∑' depth : ℕ, (((index+depth+1 : ℕ) : ℝ))*freezingRatio lower upper regularity^depth) atTop (𝓝 0) := by
    simpa only [freezing_depth_factor lower_positive upper_positive, pow_one, mul_zero, mul_assoc] using
      vanishing.const_mul errorConstant
  have local_density : ∀ᶠ index : ℕ in atTop, ∃ initial : Lp ℝ 2 volume,
      (1/2 ≤ ∫ point in good ∩ closedBall centre (width*centre^index), initial point) ∧
      ‖initial‖^2 ≤ (initialL2Constant*width)/(width*centre^index) := by
    filter_upwards [kernels, window_inside,
      total_error_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))]
      with index kernels window_inside error_small
    obtain ⟨index_positive, vertical_positive, root, freezing, densities, density, root_continuous,
      root_window, root_zero, root_unique, derivative_negative, finite_energy, energy_average,
      nonnegative, laws, convergence, initial_exists, error_bound, root_law⟩ := kernels
    obtain ⟨initial, initial_representative, initial_bound⟩ := initial_exists
    have rho_positive : 0 < centre^index := pow_pos centre_positive index
    have root_distance : ∀ digits, |root digits-centre| ≤ width*centre^index := by
      intro digits
      apply abs_le.mpr
      constructor <;> linarith [(root_window digits).1, (root_window digits).2]
    have window_ordered : centre-width*centre^index ≤ centre+width*centre^index := by
      have : 0 < width*centre^index := by positivity
      linarith
    have left_inside := window_inside (centre-width*centre^index)
      (by rw [show centre-width*centre^index-centre = -(width*centre^index) by ring,
        abs_neg, abs_of_pos (mul_pos width_positive rho_positive)])
    have right_inside := window_inside (centre+width*centre^index)
      (by rw [show centre+width*centre^index-centre = width*centre^index by ring,
        abs_of_pos (mul_pos width_positive rho_positive)])
    have interval_inside : Icc (centre-width*centre^index) (centre+width*centre^index) ⊆ Icc lower upper := by
      intro point point_inside
      exact ⟨left_inside.1.le.trans point_inside.1, point_inside.2.trans right_inside.2.le⟩
    have differentiable : ∀ digits, DifferentiableAt ℝ
        (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) (root digits) := by
      intro digits
      have positive := lower_positive.trans_le (interval_inside (root_window digits)).1
      have less_one := (interval_inside (root_window digits)).2.trans_lt upper_less_one
      have horizontal_positive : 0 < centeredHorizontalFactor index (fun position => (digits position).1) (root digits) := by
        have tail_small : (root digits)^index < 1 := pow_lt_one₀ positive.le less_one (by omega)
        have product_nonnegative := mul_nonneg (pow_nonneg positive.le index)
          (address_nonnegative positive.le less_one (fun position => (digits position).1))
        unfold centeredHorizontalFactor
        linarith
      exact (centeredNormalizedResidual_hasDerivAt exponent (horizontalDepth index) (verticalDepth index) index digits
        positive less_one horizontal_positive (pow_lt_one₀ positive.le less_one (by omega))).differentiableAt
    let data := centeredRootFibreData exponent_greater_one
      (lower_quarter.trans left_inside.1) (right_inside.2.trans upper_half) window_ordered
      (horizontalDepth index) (verticalDepth index) index vertical_positive index_positive root root_window root_unique
      slope_positive differentiable (fun digits => derivative_negative digits (root digits) (root_window digits))
    have root_dimension := (First.Roots.root_fibres data).2
    letI : IsProbabilityMeasure (First.Roots.rootLaw root) := First.Roots.rootLaw_probability root root_continuous.measurable
    have window_mass := First.Roots.rootLaw_parameter_band root root_continuous.measurable
      (centre-width*centre^index) (centre+width*centre^index) root_window
    have window_ae : ∀ᵐ point ∂First.Roots.rootLaw root,
        point ∈ Icc (centre-width*centre^index) (centre+width*centre^index) :=
      (mem_ae_iff_prob_eq_one measurableSet_Icc).mpr window_mass
    have full_mass_ae : ∀ᵐ point ∂First.Roots.rootLaw root,
        point ∈ good ∩ closedBall centre (width*centre^index) := by
      filter_upwards [root_dimension, window_ae] with point equality point_inside
      refine ⟨⟨interval_inside point_inside, equality⟩, ?_⟩
      rw [Real.closedBall_eq_Icc]
      exact point_inside
    have full_mass : First.Roots.rootLaw root (good ∩ closedBall centre (width*centre^index)) = 1 :=
      (mem_ae_iff_prob_eq_one (good_measurable.inter measurableSet_closedBall)).mp full_mass_ae
    have density_nonnegative : 0 ≤ density :=
      (isClosed_Ici : IsClosed (Set.Ici (0 : Lp ℝ 1 volume))).mem_of_tendsto
        convergence (Eventually.of_forall nonnegative)
    have integral_mass : (∫ point in good ∩ closedBall centre (width*centre^index), density point) = 1 := by
      rw [setIntegral_eq_real_measure_of_density (First.Roots.rootLaw root) density density_nonnegative
        root_law _ (good_measurable.inter measurableSet_closedBall), measureReal_def, full_mass, ENNReal.toReal_one]
    have transfer := abs_setIntegral_sub_le_L1_norm density (densities 0)
      (good ∩ closedBall centre (width*centre^index))
    rw [integral_mass] at transfer
    have half_mass : 1/2 ≤ ∫ point in good ∩ closedBall centre (width*centre^index), densities 0 point := by
      have total_small := error_bound.trans_lt error_small
      have lower := (le_abs_self (1-∫ point in good ∩ closedBall centre (width*centre^index), densities 0 point)).trans transfer
      linarith
    refine ⟨initial, ?_, initial_bound.trans_eq ?_⟩
    · apply half_mass.trans_eq
      exact integral_congr_ae (ae_restrict_of_ae initial_representative.symm)
    · field_simp [width_positive.ne', rho_positive.ne']
  let initial : ℕ → Lp ℝ 2 volume := fun index => Classical.epsilon (fun density : Lp ℝ 2 volume =>
    (1/2 ≤ ∫ point in good ∩ closedBall centre (width*centre^index), density point) ∧
      ‖density‖^2 ≤ (initialL2Constant*width)/(width*centre^index))
  have estimates : ∀ᶠ index : ℕ in atTop,
      (1/2 ≤ ∫ point in good ∩ closedBall centre (width*centre^index), initial index point) ∧
      ‖initial index‖^2 ≤ (initialL2Constant*width)/(width*centre^index) := by
    filter_upwards [local_density] with index density_exists
    exact Classical.epsilon_spec density_exists
  refine ⟨(fun index => width*centre^index), initialL2Constant*width, initial, by positivity,
    (fun index => by positivity), ?_, estimates⟩
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨by simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one centre_positive.le centre_less_one).const_mul width,
    Eventually.of_forall (fun index => mul_pos width_positive (pow_pos centre_positive index))⟩

/-- The frozen manuscript's full a.e. dimension conclusion, by a countable
cover of genuine admissible windows. This theorem uses the actual internal
root-fibre theorem, not an assumed full-mass conclusion. -/
theorem irrational_ae_dimension_equality
    {exponent : ℝ} (irrational : Irrational exponent) (exponent_greater_one : 1 < exponent) :
    ∀ᵐ ratio : ℝ, ratio ∈ Ioo (Real.sqrt 3/4) (1/2) →
      dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio) := by
  classical
  have windows : ∀ point : Ioo (Real.sqrt 3/4 : ℝ) (1/2), ∃ lower upper regularity : ℝ,
      Real.sqrt 3/4 < lower ∧ lower < point.val ∧ point.val < upper ∧ upper < 1/2 ∧
      0 < regularity ∧ upper^2/lower < 1 ∧
      2*regularity < 2*Real.log (8/3 : ℝ)/Real.log (upper/lower^3)-1 ∧
      (upper^2/lower)^(2*regularity) < upper^(1-Real.log 2/Real.log (1/lower)) :=
    fun point => exists_ae_exponent_window point.property.1 point.property.2
  choose lower upper regularity properties using windows
  have local_ae (point : Ioo (Real.sqrt 3/4 : ℝ) (1/2)) :
      ∀ᵐ ratio : ℝ, ratio ∈ Ioo (lower point) (upper point) →
        dimH (intersection exponent ratio) = ENNReal.ofReal (expectedDimension ratio) := by
    have bounds := properties point
    have sqrt_positive := Real.sqrt_nonneg (3 : ℝ)
    have sqrt_square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have lower_quarter : 1/4 < lower point := by nlinarith [bounds.1]
    have lower_positive : 0 < lower point := by linarith
    exact ae_dimension_equality_on_actual_admissible_band irrational exponent_greater_one lower_quarter
      (bounds.2.1.le.trans bounds.2.2.1.le) bounds.2.2.2.1
      (by have product := (div_lt_one lower_positive).mp bounds.2.2.2.2.2.1; simpa only [pow_two] using product)
      bounds.2.2.2.2.1 bounds.2.2.2.2.2.2.1 bounds.2.2.2.2.2.2.2
  obtain ⟨cover, countable, covers⟩ :=
    (HereditarilyLindelofSpace.isLindelof (Ioo (Real.sqrt 3/4 : ℝ) (1/2))).elim_countable_subcover
      (fun point => Ioo (lower point) (upper point)) (fun _ => isOpen_Ioo)
      (by intro ratio inside; exact mem_iUnion.mpr ⟨⟨ratio, inside⟩, (properties ⟨ratio, inside⟩).2.1,
        (properties ⟨ratio, inside⟩).2.2.1⟩)
  letI : Countable cover := countable.to_subtype
  filter_upwards [ae_all_iff.mpr (fun point : cover => local_ae point.val)] with ratio all_windows
  intro inside
  obtain ⟨point, point_mem, ratio_inside⟩ := mem_iUnion₂.mp (covers inside)
  exact all_windows ⟨point, point_mem⟩ ratio_inside

end LambdaCantor.AE

#print axioms LambdaCantor.AE.irrational_ae_dimension_equality
