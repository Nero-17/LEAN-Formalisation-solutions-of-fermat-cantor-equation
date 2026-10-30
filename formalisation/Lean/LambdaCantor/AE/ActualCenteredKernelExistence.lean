import LambdaCantor.AE.FreezingAverageEnergy
import LambdaCantor.AE.CenteredPrefixAverageAE
import LambdaCantor.AE.CenteredActualC2Families
import LambdaCantor.AE.CenteredPrefixTopology
import LambdaCantor.AE.CenteredUniformMixed
import LambdaCantor.AE.CenteredSmallBallActual
import LambdaCantor.AE.ActualParentFreezeTransport
import LambdaCantor.AE.InitialKernelL2
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace LambdaCantor.AE

/-- Construct the measurable actual root maps on their original shrinking
windows, preserving the independently expanded derivative window. -/
theorem irrational_actual_continuous_centered_families
    {exponent centre lower upper : ℝ}
    (irrational : Irrational exponent) (exponent_greater_one : 1 < exponent)
    (lower_positive : 0 < lower) (centre_lower : lower < centre) (centre_upper : centre < upper)
    (upper_less_one : upper < 1) :
    ∃ horizontalDepth verticalDepth : ℕ → ℕ, ∃ width slope firstBound secondBound : ℝ,
      0 < width ∧ 0 < slope ∧ 0 < firstBound ∧ 0 < secondBound ∧
      (∀ index, index ≤ horizontalDepth index ∧ index ≤ verticalDepth index ∧ 2 ≤ verticalDepth index) ∧
      (∀ index, |(verticalDepth index : ℝ)-exponent*horizontalDepth index +
        Real.log exponent/Real.log centre| < (centre^index)^2 ∧
        (verticalDepth index : ℝ)^2*upper^verticalDepth index < (centre^index)^3) ∧
      ∀ expansion : ℝ, 0 ≤ expansion → ∀ᶠ index : ℕ in atTop,
        ∃ root : (ℕ → Bool × Bool) → ℝ, Continuous root ∧
          (∀ digits, root digits ∈ Icc (centre-width*centre^index) (centre+width*centre^index)) ∧
          (∀ digits, centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index
            digits (root digits) = 0) ∧
          (∀ digits ratio, ratio ∈ Icc (centre-width*centre^index) (centre+width*centre^index) →
            centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits ratio = 0 →
              ratio = root digits) ∧
          ∀ digits ratio, ratio ∈ Icc lower upper → |ratio-centre| ≤ (width+expansion)*centre^index →
            deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) ratio ≤ -slope ∧
            |deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) ratio| ≤ firstBound ∧
            |centeredNormalizedSecond exponent (horizontalDepth index) (verticalDepth index) index digits ratio| ≤ secondBound := by
  classical
  obtain ⟨horizontalDepth, verticalDepth, width, slope, firstBound, secondBound,
    width_positive, slope_positive, first_positive, second_positive, depths, choices, families⟩ :=
    irrational_centered_C2_families_expanded irrational exponent_greater_one lower_positive
      centre_lower centre_upper upper_less_one
  have centre_positive := lower_positive.trans centre_lower
  have centre_less_one := centre_upper.trans upper_less_one
  have inside := centered_window_eventually_mem_nhds (windowConstant := width)
    centre_positive centre_less_one (Ioo_mem_nhds centre_lower centre_upper)
  refine ⟨horizontalDepth, verticalDepth, width, slope, firstBound, secondBound,
    width_positive, slope_positive, first_positive, second_positive, depths, choices, ?_⟩
  intro expansion expansion_nonnegative
  filter_upwards [families expansion expansion_nonnegative, inside] with index family inside
  have endpoints : lower < centre-width*centre^index ∧ centre+width*centre^index < upper := by
    have positive : 0 ≤ width*centre^index := by positivity
    constructor
    · apply (inside (centre-width*centre^index) ?_).1
      rw [show centre-width*centre^index-centre = -(width*centre^index) by ring,
        abs_neg, abs_of_nonneg positive]
    · apply (inside (centre+width*centre^index) ?_).2
      rw [show centre+width*centre^index-centre = width*centre^index by ring,
        abs_of_nonneg positive]
  have window_ordered : centre-width*centre^index ≤ centre+width*centre^index := by
    have : 0 ≤ width*centre^index := by positivity
    linarith
  obtain ⟨root, root_continuous, root_inside, root_zero⟩ :=
    exists_continuous_centered_root (by linarith : 0 < exponent)
      (lower_positive.trans endpoints.1) (endpoints.2.trans upper_less_one) window_ordered
      (horizontalDepth index) (verticalDepth index) index family.1
  refine ⟨root, root_continuous, root_inside, root_zero, ?_, family.2⟩
  intro digits ratio ratio_inside ratio_zero
  obtain ⟨unique, properties, uniqueness⟩ := family.1 digits
  exact (uniqueness ratio ⟨ratio_inside, ratio_zero⟩).trans
    (uniqueness (root digits) ⟨root_inside digits, root_zero digits⟩).symm

/-- The actual Fourier averaging theorem supplies all three selection inputs:
local integrability, finiteness outside a null set, and a linear local average.
In particular no conclusion is drawn from the real value of an infinite energy. -/
theorem ae_actual_fourier_freezing_window_data
    {lower upper regularity : ℝ} (lower_positive : 0 < lower) (ordered : lower ≤ upper)
    (upper_half : upper < 1/2) (regularity_nonnegative : 0 ≤ regularity)
    (range_bound : 2*regularity <
      2*Real.log (8/3 : ℝ)/Real.log (upper/lower^3)-1) :
    ∀ᵐ centre : ℝ, centre ∈ Ioo lower upper → ∃ constant : ℝ, 0 < constant ∧
      ∀ window : ℝ, 0 < window → ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ),
        Icc (centre-window*rho) (centre+window*rho) ⊆ Ioo lower upper ∧
        IntegrableOn (fun point => 1+(fullFourierEnergy point regularity).toReal)
          (Icc (centre-window*rho) (centre+window*rho)) ∧
        (∀ᵐ point ∂volume.restrict (Icc (centre-window*rho) (centre+window*rho)),
          fullFourierEnergy point regularity < ⊤) ∧
        (∫ point in Icc (centre-window*rho) (centre+window*rho),
          1+(fullFourierEnergy point regularity).toReal) ≤ constant*window*rho := by
  have locally_integrable := locallyIntegrableOn_fullFourierEnergy
    lower_positive ordered upper_half regularity_nonnegative range_bound
  have finite_ae := ae_finite_fullFourierEnergy_on_interval
    lower_positive ordered upper_half regularity_nonnegative range_bound
  filter_upwards [ae_fullFourierEnergy_window_integral_bound
    lower_positive ordered upper_half regularity_nonnegative range_bound] with centre average
  intro centre_inside
  obtain ⟨constant, average⟩ := average centre_inside
  refine ⟨max constant 0+2, by positivity, ?_⟩
  intro window window_positive
  have identity_limit : Tendsto (fun rho : ℝ => rho) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have left_limit : Tendsto (fun rho : ℝ => centre-window*rho)
      (𝓝[>] (0 : ℝ)) (𝓝 centre) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (identity_limit.const_mul window)
  have right_limit : Tendsto (fun rho : ℝ => centre+window*rho)
      (𝓝[>] (0 : ℝ)) (𝓝 centre) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (identity_limit.const_mul window)
  filter_upwards [average window window_positive,
    left_limit.eventually (lt_mem_nhds centre_inside.1),
    right_limit.eventually (gt_mem_nhds centre_inside.2), self_mem_nhdsWithin]
    with rho average left_inside right_inside rho_positive
  have contained : Icc (centre-window*rho) (centre+window*rho) ⊆ Ioo lower upper := by
    intro point point_mem
    exact ⟨left_inside.trans_le point_mem.1, point_mem.2.trans_lt right_inside⟩
  have integrable := locally_integrable.integrableOn_compact_subset contained isCompact_Icc
  have integrable_one : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Icc (centre-window*rho) (centre+window*rho)) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine ⟨contained, integrable_one.add integrable, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae (s := Icc (centre-window*rho) (centre+window*rho)) finite_ae,
      ae_restrict_mem measurableSet_Icc] with point finite point_mem
    exact finite (contained point_mem)
  · rw [integral_add integrable_one integrable]
    have integral_one : (∫ _ : ℝ in Icc (centre-window*rho) (centre+window*rho), (1 : ℝ)) =
        2*window*rho := by
      rw [setIntegral_const]
      simp only [measureReal_def, Real.volume_Icc, smul_eq_mul, mul_one]
      rw [ENNReal.toReal_ofReal (by
        nlinarith [mul_nonneg window_positive.le rho_positive.le] :
          0 ≤ centre+window*rho-(centre-window*rho))]
      ring
    rw [integral_one]
    rw [Real.closedBall_eq_Icc] at average
    have enlarged := mul_le_mul_of_nonneg_right (le_max_left constant 0)
      (mul_nonneg window_positive.le rho_positive.le)
    nlinarith

/-- Every prefix depth receives genuine finite-energy freezing points and the
same weighted energy constant. The geometric hypotheses describe the actual
root family; all Fourier/selection inputs come from the actual average above. -/
theorem actual_finite_energy_freezing_all_depths
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root)
    {centre rho upper regularity dimension displacementConstant smallBallConstant
      windowConstant averageConstant : ℝ}
    (rho_positive : 0 < rho) (upper_positive : 0 < upper) (upper_less_one : upper < 1)
    (displacement_positive : 0 < displacementConstant) (smallBall_nonnegative : 0 ≤ smallBallConstant)
    (roots_window : ∀ digits, |root digits-centre| ≤ windowConstant*rho)
    (prefix_displacement : ∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
      (∀ position < depth, first position = second position) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (small_ball : ∀ left right : ℝ, left ≤ right →
      First.Roots.rootLaw root (Icc left right) ≤
        ENNReal.ofReal (smallBallConstant*((right-left)/rho)^dimension))
    (integrable : IntegrableOn (fun point => 1+(fullFourierEnergy point regularity).toReal)
      (Icc (centre-(windowConstant+displacementConstant)*rho)
        (centre+(windowConstant+displacementConstant)*rho)))
    (finite_ae : ∀ᵐ point ∂volume.restrict
      (Icc (centre-(windowConstant+displacementConstant)*rho)
        (centre+(windowConstant+displacementConstant)*rho)),
      fullFourierEnergy point regularity < ⊤)
    (local_average : (∫ point in
      Icc (centre-(windowConstant+displacementConstant)*rho)
        (centre+(windowConstant+displacementConstant)*rho),
      1+(fullFourierEnergy point regularity).toReal) ≤ averageConstant*rho) :
    ∃ freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ,
      (∀ depth word, freezing depth word ∈
        centeredFreezingInterval root depth displacementConstant rho upper word) ∧
      (∀ depth word, fullFourierEnergy (freezing depth word) regularity < ⊤) ∧
      ∀ depth, (∑ word, (1/4 : ℝ)^depth *
        (1+(fullFourierEnergy (freezing depth word) regularity).toReal)) ≤
        (2*(smallBallConstant*(4*displacementConstant)^dimension)*averageConstant/
          (2*displacementConstant))*upper^(-(depth : ℝ)*(1-dimension)) := by
  classical
  have selected : ∀ depth : ℕ, ∃ freezing : (Fin depth → Bool × Bool) → ℝ,
      (∀ word, freezing word ∈ centeredFreezingInterval root depth displacementConstant rho upper word) ∧
      (∀ word, fullFourierEnergy (freezing word) regularity < ⊤) ∧
      (∑ word, (1/4 : ℝ)^depth*(1+(fullFourierEnergy (freezing word) regularity).toReal)) ≤
        (2*(smallBallConstant*(4*displacementConstant)^dimension)*averageConstant/
          (2*displacementConstant))*upper^(-(depth : ℝ)*(1-dimension)) := by
    intro depth
    exact centered_freezing_average_with_ae_property root root_measurable depth
      rho_positive upper_positive upper_less_one displacement_positive smallBall_nonnegative
      roots_window (prefix_displacement depth) small_ball
      (fun point => 1+(fullFourierEnergy point regularity).toReal)
      (fun point => fullFourierEnergy point regularity < ⊤) finite_ae integrable
      (fun _ => by positivity) local_average
  choose freezing inside finite bound using selected
  exact ⟨freezing, inside, finite, bound⟩

/-- The actual averaging proof now discharges every analytic hypothesis of
the simultaneous selector. Only the root-window, prefix and small-ball
geometry remains to be supplied by the concrete centered family. -/
theorem ae_actual_finite_energy_freezing_from_root_geometry
    {lower upper regularity : ℝ} (lower_positive : 0 < lower) (ordered : lower ≤ upper)
    (upper_half : upper < 1/2) (regularity_nonnegative : 0 ≤ regularity)
    (range_bound : 2*regularity <
      2*Real.log (8/3 : ℝ)/Real.log (upper/lower^3)-1) :
    ∀ᵐ centre : ℝ, centre ∈ Ioo lower upper → ∃ constant : ℝ, 0 < constant ∧
      ∀ (windowConstant displacementConstant : ℝ), 0 ≤ windowConstant → 0 < displacementConstant →
      ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ),
      ∀ (root : (ℕ → Bool × Bool) → ℝ) (dimension smallBallConstant : ℝ),
        Measurable root → 0 ≤ smallBallConstant →
        (∀ digits, |root digits-centre| ≤ windowConstant*rho) →
        (∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
          (∀ position < depth, first position = second position) →
          |root first-root second| ≤ displacementConstant*rho*upper^depth) →
        (∀ left right : ℝ, left ≤ right → First.Roots.rootLaw root (Icc left right) ≤
          ENNReal.ofReal (smallBallConstant*((right-left)/rho)^dimension)) →
        ∃ freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ,
          (∀ depth word, freezing depth word ∈
            centeredFreezingInterval root depth displacementConstant rho upper word) ∧
          (∀ depth word, fullFourierEnergy (freezing depth word) regularity < ⊤) ∧
          ∀ depth, (∑ word, (1/4 : ℝ)^depth *
            (1+(fullFourierEnergy (freezing depth word) regularity).toReal)) ≤
            (2*(smallBallConstant*(4*displacementConstant)^dimension)*
              (constant*(windowConstant+displacementConstant))/(2*displacementConstant))*
              upper^(-(depth : ℝ)*(1-dimension)) := by
  filter_upwards [ae_actual_fourier_freezing_window_data
    lower_positive ordered upper_half regularity_nonnegative range_bound] with centre data
  intro centre_inside
  obtain ⟨constant, constant_positive, data⟩ := data centre_inside
  refine ⟨constant, constant_positive, ?_⟩
  intro windowConstant displacementConstant window_nonnegative displacement_positive
  have window_positive : 0 < windowConstant+displacementConstant := by linarith
  filter_upwards [data (windowConstant+displacementConstant) window_positive,
    self_mem_nhdsWithin] with rho data rho_positive
  intro root dimension smallBallConstant root_measurable smallBall_nonnegative
    roots_window prefix_displacement small_ball
  exact actual_finite_energy_freezing_all_depths root root_measurable rho_positive
    (lower_positive.trans_le ordered) (by linarith) displacement_positive smallBall_nonnegative
    roots_window prefix_displacement small_ball data.2.1 data.2.2.1 data.2.2.2

private theorem centered_baseline_deriv_eq_representative
    (exponent : ℝ) (horizontalDepth verticalDepth tailDepth depth : ℕ)
    (word : Fin depth → Bool × Bool) {ratio : ℝ} (positive : 0 < ratio) (less_one : ratio < 1) :
    deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) ratio =
      deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth
        (centeredPrefixRepresentative depth word)) ratio := by
  have word_identity : (fun index : Fin depth => centeredPrefixRepresentative depth word index) = word := by
    funext index
    simp only [centeredPrefixRepresentative, dif_pos index.isLt]
  have zero_identity : pairedZeroPrefixDigits depth (centeredPrefixRepresentative depth word) =
      centeredPrefixRepresentative depth word := by
    funext index
    by_cases before : index < depth <;>
      simp [pairedZeroPrefixDigits, zeroPrefixDigits, centeredPrefixRepresentative, before]
  have functions_equal : centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word =ᶠ[𝓝 ratio]
      centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth (centeredPrefixRepresentative depth word) := by
    filter_upwards [Ioo_mem_nhds positive less_one] with parameter inside
    simpa only [word_identity, zero_identity] using
      centeredPrefixBaseline_eq_normalized exponent horizontalDepth verticalDepth tailDepth depth
        (centeredPrefixRepresentative depth word) inside.1 inside.2
  exact functions_equal.deriv_eq

private theorem actual_initial_L2_density_of_width_bounds
    (kernel : FrozenNewtonKernel) (initialDensity : Lp ℝ 1 volume)
    {minimum rho regularity averageConstant : ℝ}
    (minimum_positive : 0 < minimum) (rho_positive : 0 < rho)
    (first_lower : minimum*rho ≤ kernel.firstScale) (second_lower : minimum*rho ≤ kernel.secondScale)
    (regularity_nonnegative : 0 ≤ regularity)
    (energy_finite : fullFourierEnergy kernel.freezing regularity < ⊤)
    (energy_bound : (fullFourierEnergy kernel.freezing regularity).toReal ≤ averageConstant)
    (nonnegative : 0 ≤ initialDensity)
    (law : kernel.law = volume.withDensity (fun value => ENNReal.ofReal (initialDensity value))) :
    ∃ initial : Lp ℝ 2 volume, (initial : ℝ → ℝ) =ᵐ[volume] initialDensity ∧
      ‖initial‖^2 ≤ (2*minimum⁻¹*averageConstant)/rho := by
  have affine_law : kernel.law = affineConvolutionProbability kernel.freezing kernel.affineCenter
      kernel.firstScale kernel.secondScale := by
    simpa only [normalizedNewtonLaw, sub_zero, div_one, Measure.map_id'] using
      normalizedNewtonLaw_eq_affine kernel 0 1
  obtain ⟨density, integrable, square_integrable, density_nonnegative, density_law, bound⟩ :=
    exists_affine_density_sharp_L2 (shift := kernel.affineCenter)
      (mul_pos minimum_positive rho_positive) first_lower second_lower
      regularity_nonnegative energy_finite
  have same_law : volume.withDensity (fun value => ENNReal.ofReal (density value)) =
      volume.withDensity (fun value => ENNReal.ofReal (initialDensity value)) :=
    density_law.symm.trans (affine_law.symm.trans law)
  have same_ennreal := (withDensity_eq_iff_of_sigmaFinite integrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Lp.aestronglyMeasurable initialDensity).aemeasurable.ennreal_ofReal).mp same_law
  have same : density =ᵐ[volume] initialDensity := by
    filter_upwards [same_ennreal, density_nonnegative, (Lp.coeFn_nonneg initialDensity).mpr nonnegative]
      with value equality first_nonnegative second_nonnegative
    have equality := congrArg ENNReal.toReal equality
    simpa only [ENNReal.toReal_ofReal first_nonnegative, ENNReal.toReal_ofReal second_nonnegative] using equality
  let initial := square_integrable.toLp density
  have representative : (initial : ℝ → ℝ) =ᵐ[volume] density := square_integrable.coeFn_toLp
  have norm_identity : ‖initial‖^2 = ∫ value : ℝ, |density value|^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [representative] with value equality
    simp only [equality, real_inner_self_eq_norm_sq, Real.norm_eq_abs]
  refine ⟨initial, representative.trans same, ?_⟩
  rw [norm_identity]
  have bound_finite : 2*(ENNReal.ofReal (minimum*rho)⁻¹*fullFourierEnergy kernel.freezing regularity) < ⊤ :=
    ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top energy_finite)
  have real_bound := ENNReal.toReal_mono bound_finite.ne bound
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)), ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_pos minimum_positive rho_positive).le)] at real_bound
  apply real_bound.trans
  calc
    _ ≤ 2*((minimum*rho)⁻¹*averageConstant) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left energy_bound
        (inv_nonneg.mpr (mul_pos minimum_positive rho_positive).le)) (by norm_num)
    _ = _ := by field_simp [minimum_positive.ne', rho_positive.ne']

/-- The actual centered families and the actual Fourier average produce
convergent actual Newton densities. Every geometric, finite-energy and
weighted-average input of the global replacement theorem is discharged here. -/
theorem ae_irrational_actual_centered_kernel_limits
    {exponent lower upper regularity : ℝ}
    (irrational : Irrational exponent) (exponent_greater_one : 1 < exponent)
    (lower_positive : 0 < lower) (ordered : lower ≤ upper) (upper_half : upper < 1/2)
    (square_less : upper*upper < lower) (regularity_positive : 0 < regularity)
    (regularity_le_one : regularity ≤ 1)
    (range_bound : 2*regularity < 2*Real.log (8/3 : ℝ)/Real.log (upper/lower^3)-1)
    (summability_room : (upper^2/lower)^(2*regularity) <
      upper^(1-Real.log 2/Real.log (1/lower))) :
    ∀ᵐ centre : ℝ, centre ∈ Ioo lower upper →
      ∃ horizontalDepth verticalDepth : ℕ → ℕ, ∃ width slope averageConstant errorConstant initialL2Constant : ℝ,
        0 < width ∧ 0 < slope ∧ 0 < averageConstant ∧ 0 ≤ errorConstant ∧ 0 < initialL2Constant ∧
        ∀ᶠ index : ℕ in atTop, 1 ≤ index ∧ 1 ≤ verticalDepth index ∧
          ∃ (root : (ℕ → Bool × Bool) → ℝ)
            (freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
            (densities : ℕ → Lp ℝ 1 volume) (density : Lp ℝ 1 volume),
            Continuous root ∧
            (∀ digits, root digits ∈ Icc (centre-width*centre^index) (centre+width*centre^index)) ∧
            (∀ digits, centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index
              digits (root digits) = 0) ∧
            (∀ digits ratio, ratio ∈ Icc (centre-width*centre^index) (centre+width*centre^index) →
              (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits ratio = 0 ↔
                ratio = root digits)) ∧
            (∀ digits ratio, ratio ∈ Icc (centre-width*centre^index) (centre+width*centre^index) →
              deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) ratio ≤ -slope) ∧
            (∀ depth word, fullFourierEnergy (freezing depth word) regularity < ⊤) ∧
            (∀ depth, (∑ word, (1/4 : ℝ)^depth*(1+(fullFourierEnergy (freezing depth word) regularity).toReal)) ≤
              averageConstant*upper^(-(depth : ℝ)*(1-Real.log 2/Real.log (1/lower)))) ∧
            (∀ depth, 0 ≤ densities depth) ∧
            (∀ depth, First.Roots.pairedAddressMeasure.map
              (newtonMixtureObservable depth (fun word => centeredFrozenNewton exponent
                (horizontalDepth index) (verticalDepth index) index depth word (freezing depth word))) =
                  volume.withDensity (fun value => ENNReal.ofReal (densities depth value))) ∧
            Tendsto densities atTop (𝓝 density) ∧
            (∃ initial : Lp ℝ 2 volume, (initial : ℝ → ℝ) =ᵐ[volume] densities 0 ∧
              ‖initial‖^2 ≤ initialL2Constant/(centre^index)) ∧
            ‖density-densities 0‖ ≤ errorConstant*(centre^index)^(regularity/(1+regularity))*
              ∑' depth : ℕ, (((index+depth+1 : ℕ) : ℝ))*freezingRatio lower upper regularity^depth ∧
            First.Roots.pairedAddressMeasure.map root =
              volume.withDensity (fun value => ENNReal.ofReal (density value)) := by
  classical
  have upper_positive := lower_positive.trans_le ordered
  have upper_less_one : upper < 1 := by linarith
  filter_upwards [ae_actual_finite_energy_freezing_from_root_geometry lower_positive ordered upper_half
    regularity_positive.le range_bound] with centre selection
  intro centre_inside
  have centre_positive := lower_positive.trans centre_inside.1
  have centre_less_one := centre_inside.2.trans upper_less_one
  obtain ⟨selectionConstant, selection_positive, selection⟩ := selection centre_inside
  obtain ⟨horizontalDepth, verticalDepth, width, slope, firstBound, secondBound,
    width_positive, slope_positive, first_positive, second_positive, depths, choices, families⟩ :=
    irrational_actual_continuous_centered_families irrational exponent_greater_one lower_positive
      centre_inside.1 centre_inside.2 upper_less_one
  let target := -(Real.log exponent/Real.log centre)
  let discrepancyBound := |target|+1
  let normalizedBound := lower^(-discrepancyBound)
  let coefficientBound := exponent*normalizedBound
  let displacementConstant := 2*(exponent+coefficientBound)/slope
  let dimension := Real.log (1/2 : ℝ)/Real.log lower
  let smallBallConstant := ((4*firstBound)/
    ((exponent*(1/2 : ℝ)^(exponent-1))*(1-2*upper)*lower))^dimension
  have exponent_positive : 0 < exponent := by linarith
  have discrepancy_nonnegative : 0 ≤ discrepancyBound := by dsimp [discrepancyBound]; positivity
  have normalized_positive : 0 < normalizedBound := Real.rpow_pos_of_pos lower_positive _
  have coefficient_positive : 0 < coefficientBound := mul_pos exponent_positive normalized_positive
  have displacement_positive : 0 < displacementConstant := by dsimp [displacementConstant]; positivity
  have smallBall_positive : 0 < smallBallConstant := centered_smallBall_constant_positive
    exponent_greater_one.le lower_positive upper_half first_positive
  have dimension_identity : dimension = Real.log 2/Real.log (1/lower) := by
    dsimp [dimension]
    rw [one_div, Real.log_inv, one_div, Real.log_inv]
    ring
  have phase : ∀ index, |(verticalDepth index : ℝ)-exponent*horizontalDepth index-target| ≤ (centre^index)^2 := by
    intro index
    simpa only [target, sub_neg_eq_add] using (choices index).1.le
  have decay : ∀ index, (verticalDepth index : ℝ)^2*upper^verticalDepth index ≤ (centre^index)^3 :=
    fun index => (choices index).2.le
  obtain ⟨mixedBound, mixed_positive, mixed⟩ := centered_uniform_mixed_bound exponent_greater_one centre_positive
    centre_less_one lower_positive ordered upper_less_one (add_nonneg width_positive.le displacement_positive.le)
    horizontalDepth verticalDepth (fun index => ⟨(depths index).2.1,
      le_trans (by decide : 1 ≤ 2) (depths index).2.2⟩) phase decay
  let averageConstant := 2*(smallBallConstant*(4*displacementConstant)^dimension)*
    (selectionConstant*(width+displacementConstant))/(2*displacementConstant)
  have average_positive : 0 < averageConstant := by dsimp [averageConstant]; positivity
  let minimum := actualParentUniformMinimum exponent lower discrepancyBound firstBound
  let radius := actualParentUniformRadius exponent lower discrepancyBound slope
  have radius_positive : 0 < radius :=
    actualParentUniformRadius_positive (discrepancyBound := discrepancyBound)
      exponent_greater_one lower_positive slope_positive
  let transportConstant := actualParentFreezeTransportConstant radius radius_positive.le
  let coefficient := (2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)).toReal
  let errorConstant := transportConstant*((1+coefficient)*averageConstant*
    (1+upper^(-(1-Real.log 2/Real.log (1/lower)))))^(1/(2*(1+regularity)))*
    (12*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope)^
      (regularity/(1+regularity))
  have transport_positive : 0 < transportConstant := (Classical.choose_spec
    (exists_normalized_finite_mixture_transport_constant (Index := Bool × Bool) radius_positive.le)).1
  have error_nonnegative : 0 ≤ errorConstant := by
    have coefficient_nonnegative : 0 ≤ coefficient := ENNReal.toReal_nonneg
    have exponent_minus_one_nonnegative : 0 ≤ exponent-1 :=
      sub_nonneg.mpr exponent_greater_one.le
    have parent_error_nonnegative : 0 ≤ actualParentNewtonErrorConstant
        exponent normalizedBound mixedBound secondBound displacementConstant slope := by
      unfold actualParentNewtonErrorConstant
      positivity
    change 0 ≤ transportConstant*((1+coefficient)*averageConstant*
      (1+upper^(-(1-Real.log 2/Real.log (1/lower)))))^(1/(2*(1+regularity)))*
      (12*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope)^
        (regularity/(1+regularity))
    positivity
  let initialMinimum := min (exponent*(1/2 : ℝ)^(exponent-1)/(2*firstBound))
    (exponent*lower^discrepancyBound*(1/2 : ℝ)^(exponent-1)/(2*firstBound))
  have initialMinimum_positive : 0 < initialMinimum := by dsimp [initialMinimum]; positivity
  let initialL2Constant := 2*initialMinimum⁻¹*averageConstant
  have initialL2_positive : 0 < initialL2Constant := by dsimp [initialL2Constant]; positivity
  have powers_limit : Tendsto (fun index : ℕ => centre^index) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one centre_positive.le centre_less_one,
      Eventually.of_forall (fun index => pow_pos centre_positive index)⟩
  have selected := powers_limit.eventually
    (selection width displacementConstant width_positive.le displacement_positive)
  have inside := centered_window_eventually_mem_nhds (windowConstant := width+displacementConstant)
    centre_positive centre_less_one (Ioo_mem_nhds centre_inside.1 centre_inside.2)
  have comparable := centered_window_power_comparable centre_positive centre_less_one
    (add_nonneg width_positive.le displacement_positive.le)
  have power_small : ∀ᶠ index : ℕ in atTop, upper^index ≤ (1/2 : ℝ) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one upper_positive.le upper_less_one).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have numerical := actual_parent_numerical_conditions_eventually exponent_greater_one centre_positive centre_less_one
    lower_positive upper_positive upper_less_one square_less normalized_positive.le mixed_positive.le second_positive.le
    displacement_positive.le slope_positive
  refine ⟨horizontalDepth, verticalDepth, width, slope, averageConstant, errorConstant, initialL2Constant,
    width_positive, slope_positive, average_positive, error_nonnegative, initialL2_positive, ?_⟩
  filter_upwards [families displacementConstant displacement_positive.le, mixed, selected, inside, comparable,
    power_small, numerical, eventually_ge_atTop 1] with index family mixed selected inside comparable
      power_small numerical index_positive
  obtain ⟨root, root_continuous, root_window, root_zero, root_unique, derivatives⟩ := family
  have rho_positive : 0 < centre^index := pow_pos centre_positive index
  have root_distance : ∀ digits, |root digits-centre| ≤ width*centre^index := by
    intro digits
    exact abs_le.mpr ⟨by linarith [(root_window digits).1], by linarith [(root_window digits).2]⟩
  have expanded_distance : ∀ parameter ∈ Icc (centre-width*centre^index) (centre+width*centre^index),
      |parameter-centre| ≤ (width+displacementConstant)*centre^index := by
    intro parameter parameter_inside
    apply abs_le.mpr
    have enlargement : 0 ≤ displacementConstant*centre^index := by positivity
    constructor <;> linarith [parameter_inside.1, parameter_inside.2]
  have window_inside : Icc (centre-width*centre^index) (centre+width*centre^index) ⊆ Icc lower upper := by
    intro parameter parameter_inside
    exact ⟨(inside parameter (expanded_distance parameter parameter_inside)).1.le,
      (inside parameter (expanded_distance parameter parameter_inside)).2.le⟩
  have small_powers : ∀ parameter : ℝ, |parameter-centre| ≤ (width+displacementConstant)*centre^index →
      0 < parameter ∧ parameter < 1 ∧ parameter^index ≤ 1/2 ∧ parameter^verticalDepth index ≤ 1/2 := by
    intro parameter close
    have parameter_inside := inside parameter close
    have positive := lower_positive.trans parameter_inside.1
    have tail := (pow_le_pow_left₀ positive.le parameter_inside.2.le index).trans power_small
    have vertical := ((pow_le_pow_left₀ positive.le parameter_inside.2.le (verticalDepth index)).trans
      (pow_le_pow_of_le_one upper_positive.le upper_less_one.le (depths index).2.1)).trans power_small
    exact ⟨positive, parameter_inside.2.trans upper_less_one, tail, vertical⟩
  have differentiable : ∀ digits parameter, parameter ∈ Icc (centre-width*centre^index) (centre+width*centre^index) →
      DifferentiableAt ℝ (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) parameter := by
    intro digits parameter parameter_inside
    have conditions := small_powers parameter (expanded_distance parameter parameter_inside)
    exact (centeredNormalizedResidual_hasDerivAt exponent (horizontalDepth index) (verticalDepth index) index digits
      conditions.1 conditions.2.1 (centeredHorizontalFactor_positive_of_tail_small conditions.1 conditions.2.1 index _
        conditions.2.2.1) (by linarith [conditions.2.2.2])).differentiableAt
  have derivative_negative : ∀ digits parameter, parameter ∈ Icc (centre-width*centre^index) (centre+width*centre^index) →
      deriv (centeredNormalizedResidual exponent (horizontalDepth index) (verticalDepth index) index digits) parameter ≤ -slope := by
    intro digits parameter parameter_inside
    exact (derivatives digits parameter (window_inside parameter_inside) (expanded_distance parameter parameter_inside)).1
  have phase_bound : |(verticalDepth index : ℝ)-exponent*horizontalDepth index| ≤ discrepancyBound := by
    have epsilon_one : (centre^index)^2 ≤ 1 :=
      pow_le_one₀ (pow_nonneg centre_positive.le _) (pow_le_one₀ centre_positive.le centre_less_one.le)
    calc
      _ = |((verticalDepth index : ℝ)-exponent*horizontalDepth index-target)+target| := by congr 1; ring
      _ ≤ |(verticalDepth index : ℝ)-exponent*horizontalDepth index-target|+|target| := abs_add_le _ _
      _ ≤ discrepancyBound := by dsimp [discrepancyBound]; linarith [phase index]
  have coefficient_bound : ∀ digits, exponent*(root digits)^((verticalDepth index : ℝ)-exponent*horizontalDepth index) ≤ coefficientBound := by
    intro digits
    apply mul_le_mul_of_nonneg_left _ exponent_positive.le
    exact centered_resonance_factor_bound lower_positive (window_inside (root_window digits)).1
      ((window_inside (root_window digits)).2.trans upper_less_one.le) discrepancy_nonnegative (abs_le.mp phase_bound).1
  have root_power_lower : ∀ digits, centre^index/2 ≤ (root digits)^index := by
    intro digits
    have bound := (comparable (root digits) (expanded_distance (root digits) (root_window digits))).1
    linarith
  have root_power_upper : ∀ digits, (root digits)^index ≤ 2*centre^index :=
    fun digits => (comparable (root digits) (expanded_distance (root digits) (root_window digits))).2
  have window_lower : lower ≤ centre-width*centre^index := by
    have point_inside := inside (centre-width*centre^index)
      (expanded_distance _ ⟨le_rfl, by linarith [mul_nonneg width_positive.le rho_positive.le]⟩)
    exact point_inside.1.le
  have window_upper : centre+width*centre^index ≤ upper := by
    have point_inside := inside (centre+width*centre^index)
      (expanded_distance _ ⟨by linarith [mul_nonneg width_positive.le rho_positive.le], le_rfl⟩)
    exact point_inside.2.le
  have prefix_displacement : ∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
      (∀ position < depth, first position = second position) →
      |root first-root second| ≤ displacementConstant*centre^index*upper^depth := by
    intro depth first second agreement
    exact centered_root_shared_prefix_displacement_on_window exponent_greater_one.le lower_positive upper_less_one
      window_lower window_upper rho_positive slope_positive
      coefficient_positive.le (horizontalDepth index) (verticalDepth index) index depth root root_window root_zero
      root_power_upper (fun digits => (small_powers _ (expanded_distance _ (root_window digits))).2.2.1)
      (fun digits => (small_powers _ (expanded_distance _ (root_window digits))).2.2.2) coefficient_bound
      (fun digits parameter parameter_inside => (differentiable digits parameter parameter_inside).continuousAt.continuousWithinAt)
      (fun digits parameter parameter_inside => (differentiable digits parameter ⟨parameter_inside.1.le, parameter_inside.2.le⟩).differentiableWithinAt)
      (fun digits parameter parameter_inside => derivative_negative digits parameter ⟨parameter_inside.1.le, parameter_inside.2.le⟩)
      first second agreement
  have small_ball : ∀ left right : ℝ, left ≤ right → First.Roots.rootLaw root (Icc left right) ≤
      ENNReal.ofReal (smallBallConstant*((right-left)/(centre^index))^dimension) := by
    intro left right order
    exact centered_root_interval_smallBall exponent_greater_one.le lower_positive upper_half window_lower window_upper
      rho_positive first_positive (horizontalDepth index) (verticalDepth index) index root root_continuous.measurable
      root_window root_zero root_power_lower
      (fun digits => (small_powers _ (expanded_distance _ (root_window digits))).2.2.1)
      differentiable (fun digits parameter parameter_inside =>
        (derivatives digits parameter (window_inside parameter_inside) (expanded_distance parameter parameter_inside)).2.1) order
  obtain ⟨freezing, freezing_mem, finite_energy, energy_average⟩ := selected root dimension smallBallConstant
    root_continuous.measurable smallBall_positive.le root_distance prefix_displacement small_ball
  have freezing_distance : ∀ depth word, |freezing depth word-centre| ≤ (width+displacementConstant)*centre^index := by
    intro depth
    exact centered_freezing_center_distance root depth displacement_positive.le rho_positive.le upper_positive.le upper_less_one.le
      root_distance (freezing depth) (freezing_mem depth)
  have freezing_band : ∀ depth word, freezing depth word ∈ Icc lower upper := by
    intro depth word
    exact ⟨(inside _ (freezing_distance depth word)).1.le, (inside _ (freezing_distance depth word)).2.le⟩
  have segment_distance : ∀ depth digits parameter,
      parameter ∈ uIcc (freezing depth (fun position => digits position)) (root digits) →
      |parameter-centre| ≤ (width+displacementConstant)*centre^index := by
    intro depth digits parameter parameter_inside
    have endpoints := uIcc_subset_Icc
      (show freezing depth (fun position => digits position) ∈
        Icc (centre-(width+displacementConstant)*centre^index) (centre+(width+displacementConstant)*centre^index) by
        have bound := abs_le.mp (freezing_distance depth (fun position => digits position)); constructor <;> linarith)
      (show root digits ∈ Icc (centre-(width+displacementConstant)*centre^index) (centre+(width+displacementConstant)*centre^index) by
        have bound := abs_le.mp (expanded_distance _ (root_window digits)); constructor <;> linarith)
      parameter_inside
    apply abs_le.mpr
    constructor <;> linarith [endpoints.1, endpoints.2]
  have normalized_bound : ∀ depth word, (verticalDepth index : ℝ)^2*
      ((freezing depth word)^(-exponent*(horizontalDepth index : ℝ))*((freezing depth word)^verticalDepth index)^2) ≤ normalizedBound := by
    intro depth word
    have bound := centered_normalized_quadratic_decay lower_positive (freezing_band depth word).1
      (freezing_band depth word).2 upper_less_one (horizontalDepth index) (verticalDepth index) (phase index)
      (show (centre^index)^2 ≤ 1 from pow_le_one₀ (pow_nonneg centre_positive.le _)
        (pow_le_one₀ centre_positive.le centre_less_one.le)) (decay index)
    exact bound.trans (mul_le_of_le_one_right normalized_positive.le
      (pow_le_one₀ (pow_nonneg centre_positive.le _) (pow_le_one₀ centre_positive.le centre_less_one.le)))
  have baseline_derivatives : ∀ depth word,
      deriv (centeredPrefixBaseline exponent (horizontalDepth index) (verticalDepth index) index depth word)
        (freezing depth word) ≤ -slope ∧
      |deriv (centeredPrefixBaseline exponent (horizontalDepth index) (verticalDepth index) index depth word)
        (freezing depth word)| ≤ firstBound := by
    intro depth word
    rw [centered_baseline_deriv_eq_representative exponent (horizontalDepth index) (verticalDepth index) index depth word
      (lower_positive.trans_le (freezing_band depth word).1) ((freezing_band depth word).2.trans_lt upper_less_one)]
    exact ⟨(derivatives _ _ (freezing_band depth word) (freezing_distance depth word)).1,
      (derivatives _ _ (freezing_band depth word) (freezing_distance depth word)).2.1⟩
  have energy_average' : ∀ depth, (∑ word, (1/4 : ℝ)^depth*(1+(fullFourierEnergy (freezing depth word) regularity).toReal)) ≤
      averageConstant*upper^(-(depth : ℝ)*(1-Real.log 2/Real.log (1/lower))) := by
    intro depth
    simpa only [averageConstant, dimension_identity] using energy_average depth
  obtain ⟨densities, density, nonnegative, laws, convergence, error_bound, root_law⟩ :=
    actual_freezing_L1_limit_from_selected_points exponent_greater_one lower_positive upper_positive upper_less_one square_less
      discrepancy_nonnegative slope_positive first_positive rho_positive numerical.1 regularity_positive regularity_le_one
      normalized_positive.le mixed_positive.le second_positive.le displacement_positive.le numerical.2.1
      (horizontalDepth index) (verticalDepth index) index (by have := depths index; omega) root freezing
      prefix_displacement freezing_mem freezing_band
      (fun depth digits parameter parameter_inside => small_powers parameter (segment_distance depth digits parameter parameter_inside))
      (fun depth word => by have bound := comparable _ (freezing_distance depth word); constructor <;> linarith [bound.1, bound.2])
      phase_bound normalized_bound root_zero (fun depth word => (baseline_derivatives depth word).1)
      (fun depth word => (baseline_derivatives depth word).2)
      (fun depth digits parameter parameter_inside =>
        (derivatives _ parameter ⟨(inside parameter (segment_distance depth digits parameter parameter_inside)).1.le,
          (inside parameter (segment_distance depth digits parameter parameter_inside)).2.le⟩
          (segment_distance depth digits parameter parameter_inside)).2.2)
      (fun depth digits parameter parameter_inside => mixed depth digits (pairedZeroPrefixDigits depth digits) parameter
        ⟨(inside parameter (segment_distance depth digits parameter parameter_inside)).1.le,
          (inside parameter (segment_distance depth digits parameter parameter_inside)).2.le⟩
        (segment_distance depth digits parameter parameter_inside) (pairedZeroPrefixDigits_agrees depth digits))
      finite_energy numerical.2.2 root_continuous.measurable averageConstant average_positive.le energy_average' summability_room
  let emptyWord : Fin 0 → Bool × Bool := Fin.elim0
  let initialKernel := centeredFrozenNewton exponent (horizontalDepth index) (verticalDepth index) index 0 emptyWord (freezing 0 emptyWord)
  have empty_univ : (Finset.univ : Finset (Fin 0 → Bool × Bool)) = {emptyWord} := by
    ext word
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  have initial_law : initialKernel.law = volume.withDensity (fun value => ENNReal.ofReal (densities 0 value)) := by
    have law := laws 0
    rw [newtonMixtureObservable_law] at law
    simpa only [empty_univ, Finset.sum_singleton, pow_zero, one_smul, initialKernel] using law
  have initial_energy_bound : (fullFourierEnergy (freezing 0 emptyWord) regularity).toReal ≤ averageConstant := by
    have bound := energy_average' 0
    simp only [empty_univ, Finset.sum_singleton, pow_zero, one_mul, Nat.cast_zero, neg_zero, zero_mul,
      Real.rpow_zero, mul_one] at bound
    linarith
  have representative_word : (fun position : Fin 0 => centeredPrefixRepresentative 0 emptyWord position) = emptyWord :=
    Subsingleton.elim _ _
  have initial_scales := centeredFrozenNewton_scale_bounds exponent_greater_one
    (lower_positive.trans_le (freezing_band 0 emptyWord).1) ((freezing_band 0 emptyWord).2.trans_lt upper_less_one)
    lower_positive (freezing_band 0 emptyWord).1 rho_positive.le discrepancy_nonnegative slope_positive first_positive
    (horizontalDepth index) (verticalDepth index) index 0 (centeredPrefixRepresentative 0 emptyWord)
    (small_powers _ (freezing_distance 0 emptyWord)).2.2.1 (small_powers _ (freezing_distance 0 emptyWord)).2.2.2
    (by have bound := comparable _ (freezing_distance 0 emptyWord); linarith [bound.1])
    (comparable _ (freezing_distance 0 emptyWord)).2 phase_bound
    (by simpa only [representative_word] using (baseline_derivatives 0 emptyWord).1)
    (by simpa only [representative_word] using (baseline_derivatives 0 emptyWord).2)
  rw [representative_word] at initial_scales
  have first_lower : initialMinimum*centre^index ≤ initialKernel.firstScale := by
    apply (mul_le_mul_of_nonneg_right (min_le_left _ _) rho_positive.le).trans
    simpa only [initialKernel, pow_zero, mul_one] using initial_scales.1.1
  have second_lower : initialMinimum*centre^index ≤ initialKernel.secondScale := by
    apply (mul_le_mul_of_nonneg_right (min_le_right _ _) rho_positive.le).trans
    simpa only [initialKernel, pow_zero, mul_one] using initial_scales.2.1
  have initialL2 := actual_initial_L2_density_of_width_bounds initialKernel (densities 0)
    initialMinimum_positive rho_positive first_lower second_lower regularity_positive.le
    (finite_energy 0 emptyWord) initial_energy_bound (nonnegative 0) initial_law
  refine ⟨index_positive, by have := depths index; omega, root, freezing, densities, density,
    root_continuous, root_window, root_zero, ?_, derivative_negative, finite_energy, energy_average', nonnegative,
    laws, convergence, initialL2, ?_, root_law⟩
  · intro digits ratio ratio_inside
    exact ⟨root_unique digits ratio ratio_inside, fun equal => equal.symm ▸ root_zero digits⟩
  · simpa only [errorConstant, transportConstant, coefficient, minimum, radius] using error_bound

end LambdaCantor.AE
