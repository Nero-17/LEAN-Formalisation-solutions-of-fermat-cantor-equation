import LambdaCantor.First.RootFibreGeometry
import LambdaCantor.First.RootsFrostman
import LambdaCantor.First.FrostmanPushforward

noncomputable section
namespace LambdaCantor.First.Roots

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- The actual two cylinder coordinates at one fixed parameter. -/
def fixedCylinderPoint {exponent : ℝ} (data : RootFibreData exponent)
    (ratio : ℝ) (digits : ℕ → Bool × Bool) : ℝ × ℝ :=
  (address ratio (cylinderDigits data.leftWord data.leftLength (fun index => (digits index).1)),
   address ratio (cylinderDigits data.rightWord data.rightLength (fun index => (digits index).2)))

theorem continuous_fixedCylinderPoint {exponent ratio : ℝ} (data : RootFibreData exponent)
    (hpositive : 0 ≤ ratio) (hlt : ratio < 1) : Continuous (fixedCylinderPoint data ratio) := by
  have hleft : Continuous (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) := by
    exact continuous_pi (fun index => continuous_fst.comp (continuous_apply index))
  have hright : Continuous (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) := by
    exact continuous_pi (fun index => continuous_snd.comp (continuous_apply index))
  exact ((continuous_address hpositive hlt).comp
    ((continuous_cylinderDigits data.leftWord data.leftLength).comp hleft)).prodMk
      ((continuous_address hpositive hlt).comp
        ((continuous_cylinderDigits data.rightWord data.rightLength).comp hright))

def fixedCylinderSeparationScale {exponent : ℝ} (data : RootFibreData exponent) (ratio : ℝ) : ℝ :=
  (1 - 2 * ratio) * ratio ^ max data.leftLength data.rightLength

/-- A ball at the fixed-cylinder separation scale fixes the paired tail prefix.
The two prescribed cylinder lengths need not be equal. -/
theorem fixedCylinderPoint_ball_subset_prefix {exponent ratio : ℝ}
    (data : RootFibreData exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (digits : ℕ → Bool × Bool) (depth : ℕ) :
    fixedCylinderPoint data ratio ⁻¹' Metric.ball (fixedCylinderPoint data ratio digits)
      (fixedCylinderSeparationScale data ratio * ratio ^ depth) ⊆ pairedPrefix digits depth := by
  intro other hother
  change dist (fixedCylinderPoint data ratio other) (fixedCylinderPoint data ratio digits) < _ at hother
  simp only [fixedCylinderPoint, Prod.dist_eq, Real.dist_eq, max_lt_iff] at hother
  have hscale : fixedCylinderSeparationScale data ratio * ratio ^ depth =
      (1 - 2 * ratio) * ratio ^ (max data.leftLength data.rightLength + depth) := by
    unfold fixedCylinderSeparationScale
    rw [pow_add]
    ring
  have hband : ratio ∈ Set.Icc ratio ratio := ⟨le_rfl, le_rfl⟩
  have hleft := close_incidence_same_prefix hpositive hhalf hband hband
    (cylinderDigits data.leftWord data.leftLength (fun index => (other index).1))
    (cylinderDigits data.leftWord data.leftLength (fun index => (digits index).1))
    (max data.leftLength data.rightLength + depth)
    (by simpa only [sub_self, abs_zero, mul_zero, add_zero, hscale] using hother.1)
  have hright := close_incidence_same_prefix hpositive hhalf hband hband
    (cylinderDigits data.rightWord data.rightLength (fun index => (other index).2))
    (cylinderDigits data.rightWord data.rightLength (fun index => (digits index).2))
    (max data.leftLength data.rightLength + depth)
    (by simpa only [sub_self, abs_zero, mul_zero, add_zero, hscale] using hother.2)
  intro index hindex
  exact Prod.ext
    (by simpa using hleft (data.leftLength + index) (by omega))
    (by simpa using hright (data.rightLength + index) (by omega))

/-- A finite geometric ball bound gives the same local real-radius power bound.
No probability or support hypothesis is hidden in this interpolation. -/
theorem geometric_ball_bound_all_radii {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (measure : Measure X) [IsFiniteMeasure measure]
    {scale ratio exponent constant : ℝ} (hscale : 0 < scale) (hratio : 0 < ratio)
    (hlt : ratio < 1) (hexponent : 0 < exponent) (hconstant : 0 < constant)
    (hbound : ∀ center : X, ∀ depth : ℕ,
      measure (Metric.ball center (scale * ratio ^ depth)) ≤
        ENNReal.ofReal (constant * (ratio ^ exponent) ^ depth)) :
    ∀ center : X, ∀ radius : ℝ, 0 < radius → radius ≤ scale →
      measure (Metric.ball center radius) ≤
        ENNReal.ofReal ((constant / (scale * ratio) ^ exponent) * radius ^ exponent) := by
  intro center radius hradius hsmall
  have hinterpolate := interpolate_geometric_mass
    (fun radius => measure.real (Metric.ball center radius) / constant)
    (fun _ _ hcomparison => div_le_div_of_nonneg_right
      (measureReal_mono (Metric.ball_subset_ball hcomparison)) hconstant.le)
    hscale hratio hlt hexponent hradius hsmall (by
      intro depth
      apply (div_le_iff₀ hconstant).2
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound center depth)
      simpa only [measureReal_def, ENNReal.toReal_ofReal
        (mul_nonneg hconstant.le (pow_nonneg (Real.rpow_nonneg hratio.le _) _)), mul_comm] using h)
  have hreal : measure.real (Metric.ball center radius) ≤
      (constant / (scale * ratio) ^ exponent) * radius ^ exponent := by
    have h := (div_le_iff₀ hconstant).1 hinterpolate
    have hpower : (radius / (scale * ratio)) ^ exponent * constant =
        (constant / (scale * ratio) ^ exponent) * radius ^ exponent := by
      rw [Real.div_rpow hradius.le (mul_pos hscale hratio).le]
      ring
    exact h.trans_eq hpower
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

/-- Positive mass and a genuine local Frostman ball estimate force the
Hausdorff lower bound through the Hausdorff-measure domination theorem. -/
theorem dimH_lower_of_local_ball_bound {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (measure : Measure X)
    {exponent constant cutoff : ℝ} (hexponent : 0 < exponent)
    (hconstant : 0 < constant) (hcutoff : 0 < cutoff)
    (hball : ∀ center : X, ∀ radius : ℝ, 0 < radius → radius < cutoff →
      measure (Metric.ball center radius) ≤ ENNReal.ofReal (constant * radius ^ exponent))
    {target : Set X} (hpositive : measure target ≠ 0) :
    ENNReal.ofReal exponent ≤ dimH target := by
  let dimensionExponent : ℝ≥0 := ⟨exponent, hexponent.le⟩
  rw [ENNReal.ofReal_eq_coe_nnreal hexponent.le]
  change (dimensionExponent : ℝ≥0∞) ≤ dimH target
  by_contra hnot
  have hdimension : dimH target < dimensionExponent := lt_of_not_ge hnot
  apply hpositive
  apply measure_zero_of_local_diameter_bound measure dimensionExponent
    (constant := ENNReal.ofReal constant) (cutoff := ENNReal.ofReal (cutoff / 2))
    (ENNReal.ofReal_ne_zero_iff.mpr hconstant) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr (by positivity))
  · intro set hset
    apply diameter_bound_of_local_ball_bound measure exponent ENNReal.ofReal_ne_top
      (fun center radius hradius hsmall => extended_ball_bound_of_real_ball_bound measure
        dimensionExponent hconstant.le hball center hradius hsmall)
    exact hset.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hcutoff).mpr (by linarith))
  · exact hdimension

/-- Eventual prefix bounds suffice: one positive-mass restriction has a common
starting depth. The measure may be any probability conditional address law,
including the conditional law of a compact good-set restriction. -/
theorem conditional_dimension_lower_of_geometric_prefix_bound {exponent ratio dimensionExponent normalizer : ℝ}
    (data : RootFibreData exponent) (conditional : Measure (ℕ → Bool × Bool))
    [IsProbabilityMeasure conditional] (hdimension : 0 < dimensionExponent)
    (hnormalizer : 0 < normalizer)
    (hfibre : ∀ᵐ digits ∂conditional, data.root digits = ratio)
    (hprefix : ∀ᵐ digits ∂conditional, ∃ minimumDepth : ℕ, ∀ depth ≥ minimumDepth,
      conditional (pairedPrefix digits depth) ≤
        ENNReal.ofReal ((ratio ^ dimensionExponent) ^ depth / normalizer)) :
    ENNReal.ofReal dimensionExponent ≤ dimH (intersection exponent ratio) := by
  obtain ⟨oneAddress, honeAddress⟩ := hfibre.exists
  have hband : ratio ∈ Set.Icc data.lower data.upper := by
    rw [← honeAddress]
    exact data.root_in_band oneAddress
  have hratio : 0 < ratio := by linarith [data.lower_gt_quarter, hband.1]
  have hhalf : ratio < 1 / 2 := hband.2.trans_lt data.upper_lt_half
  have hlt : ratio < 1 := by linarith
  let good : ℕ → Set (ℕ → Bool × Bool) := fun minimumDepth =>
    {digits | data.root digits = ratio ∧ ∀ depth ≥ minimumDepth,
      conditional (pairedPrefix digits depth) ≤
        ENNReal.ofReal ((ratio ^ dimensionExponent) ^ depth / normalizer)}
  have hcover : conditional (⋃ minimumDepth, good minimumDepth) = 1 := by
    calc
      _ = conditional Set.univ := measure_congr (by
        filter_upwards [hfibre, hprefix] with digits hroot ⟨minimumDepth, hbound⟩
        exact propext ⟨fun _ => True.intro,
          fun _ => Set.mem_iUnion.mpr ⟨minimumDepth, hroot, hbound⟩⟩)
      _ = 1 := measure_univ
  obtain ⟨minimumDepth, hgood⟩ : ∃ minimumDepth, conditional (good minimumDepth) ≠ 0 := by
    by_contra hnot
    push_neg at hnot
    have hzero := measure_iUnion_null hnot
    rw [hcover] at hzero
    exact one_ne_zero hzero
  let imageMeasure := (conditional.restrict (good minimumDepth)).map (fixedCylinderPoint data ratio)
  have hmeasurable := (continuous_fixedCylinderPoint data hratio.le hlt).measurable
  have hscale : 0 < fixedCylinderSeparationScale data ratio := by
    unfold fixedCylinderSeparationScale
    exact mul_pos (by linarith) (pow_pos hratio _)
  let scale : ℝ := fixedCylinderSeparationScale data ratio * ratio ^ minimumDepth / 2
  let constant : ℝ := (ratio ^ dimensionExponent) ^ minimumDepth / normalizer
  have hscalePositive : 0 < scale := by dsimp [scale]; positivity
  have hconstant : 0 < constant := by dsimp [constant]; positivity
  have hdiscrete : ∀ center : ℝ × ℝ, ∀ depth : ℕ,
      imageMeasure (Metric.ball center (scale * ratio ^ depth)) ≤
        ENNReal.ofReal (constant * (ratio ^ dimensionExponent) ^ depth) := by
    intro center depth
    change (conditional.restrict (good minimumDepth)).map (fixedCylinderPoint data ratio)
      (Metric.ball center (scale * ratio ^ depth)) ≤ _
    rw [Measure.map_apply hmeasurable Metric.isOpen_ball.measurableSet,
      Measure.restrict_apply (hmeasurable Metric.isOpen_ball.measurableSet)]
    rcases ((fixedCylinderPoint data ratio ⁻¹' Metric.ball center (scale * ratio ^ depth)) ∩
        good minimumDepth).eq_empty_or_nonempty with hempty | ⟨digits, hdigitsBall, hdigitsGood⟩
    · rw [hempty, measure_empty]
      exact zero_le
    apply (measure_mono (show
      (fixedCylinderPoint data ratio ⁻¹' Metric.ball center (scale * ratio ^ depth)) ∩ good minimumDepth ⊆
        pairedPrefix digits (minimumDepth + depth) from ?_)).trans
      ((hdigitsGood.2 (minimumDepth + depth) (by omega)).trans_eq ?_)
    · intro other hother
      apply fixedCylinderPoint_ball_subset_prefix data hratio hhalf digits (minimumDepth + depth)
      change dist (fixedCylinderPoint data ratio other) (fixedCylinderPoint data ratio digits) < _
      have hfirst : dist (fixedCylinderPoint data ratio other) center < scale * ratio ^ depth := hother.1
      have hsecond : dist center (fixedCylinderPoint data ratio digits) < scale * ratio ^ depth := by
        have hdigitsDistance : dist (fixedCylinderPoint data ratio digits) center <
            scale * ratio ^ depth := hdigitsBall
        simpa only [dist_comm] using hdigitsDistance
      have hequal : 2 * (scale * ratio ^ depth) =
          fixedCylinderSeparationScale data ratio * ratio ^ (minimumDepth + depth) := by
        dsimp [scale]
        rw [pow_add]
        ring
      exact (dist_triangle _ _ _).trans_lt (by rw [← hequal]; linarith)
    · congr 1
      dsimp [constant]
      rw [pow_add]
      ring
  have hmass : imageMeasure (intersection exponent ratio) ≠ 0 := by
    have hsubset : good minimumDepth ⊆ fixedCylinderPoint data ratio ⁻¹' intersection exponent ratio := by
      intro digits hdigits
      change fixedCylinderPoint data ratio digits ∈ intersection exponent ratio
      have h := rootFibreData_point_mem_intersection data digits
      rw [hdigits.1] at h
      simpa only [fixedCylinderPoint, cylinder_address hratio.le hlt, cylinderCoordinate] using h
    have hle := Measure.le_map_apply
      (μ := conditional.restrict (good minimumDepth)) hmeasurable.aemeasurable
      (intersection exponent ratio)
    rw [Measure.restrict_apply_superset hsubset] at hle
    intro hzero
    exact hgood (le_antisymm (hle.trans_eq hzero) zero_le)
  apply dimH_lower_of_local_ball_bound imageMeasure hdimension
    (constant := constant / (scale * ratio) ^ dimensionExponent)
    (cutoff := scale) (by positivity) hscalePositive (fun center radius hradius hsmall =>
      geometric_ball_bound_all_radii imageMeasure hscalePositive hratio hlt hdimension hconstant
        hdiscrete center radius hradius hsmall.le) hmass

def conditionalDimensionExponent (ratio loss : ℝ) : ℝ :=
  (Real.log (4 * ratio) - loss) / Real.log (1 / ratio)

theorem conditionalDimensionExponent_power {ratio loss : ℝ}
    (hratio : 0 < ratio) (hlt : ratio < 1) :
    ratio ^ conditionalDimensionExponent ratio loss = Real.exp (loss - Real.log (4 * ratio)) := by
  have hlog : Real.log ratio ≠ 0 := (Real.log_neg hratio hlt).ne
  rw [Real.rpow_def_of_pos hratio]
  congr 1
  unfold conditionalDimensionExponent
  rw [Real.log_div one_ne_zero hratio.ne', Real.log_one]
  field_simp [hlog]
  ring

/-- The raw prefix rate appearing after conditional Borel--Cantelli, expressed
with the manuscript's real-power convention. -/
theorem conditional_prefix_rate_identity {ratio loss : ℝ}
    (hratio : 0 < ratio) (hlt : ratio < 1) (depth : ℕ) :
    (4 * ratio) ^ (-(depth : ℝ)) * Real.exp (loss * depth) =
      (ratio ^ conditionalDimensionExponent ratio loss) ^ depth := by
  rw [conditionalDimensionExponent_power hratio hlt, ← Real.exp_nat_mul,
    Real.rpow_def_of_pos (mul_pos (by norm_num) hratio), ← Real.exp_add]
  congr 1
  ring

/-- Actual conditional prefix decay gives the actual Cantor-intersection
dimension bound, with no absolute-continuity or local-dimension premise. -/
theorem conditional_dimension_lower_of_prefix_bound {exponent ratio loss normalizer : ℝ}
    (data : RootFibreData exponent) (conditional : Measure (ℕ → Bool × Bool))
    [IsProbabilityMeasure conditional] (hnormalizer : 0 < normalizer)
    (hloss : loss < Real.log (4 * ratio))
    (hfibre : ∀ᵐ digits ∂conditional, data.root digits = ratio)
    (hprefix : ∀ᵐ digits ∂conditional, ∃ minimumDepth : ℕ, ∀ depth ≥ minimumDepth,
      conditional (pairedPrefix digits depth) ≤ ENNReal.ofReal
        ((4 * ratio) ^ (-(depth : ℝ)) * Real.exp (loss * depth) / normalizer)) :
    ENNReal.ofReal ((Real.log (4 * ratio) - loss) / Real.log (1 / ratio)) ≤
      dimH (intersection exponent ratio) := by
  obtain ⟨digits, hdigits⟩ := hfibre.exists
  have hband : ratio ∈ Set.Icc data.lower data.upper := by
    rw [← hdigits]
    exact data.root_in_band digits
  have hratio : 0 < ratio := by linarith [data.lower_gt_quarter, hband.1]
  have hlt : ratio < 1 := by linarith [data.upper_lt_half, hband.2]
  apply conditional_dimension_lower_of_geometric_prefix_bound data conditional
    (show 0 < conditionalDimensionExponent ratio loss from
      div_pos (sub_pos.mpr hloss) (Real.log_pos ((one_lt_div hratio).mpr hlt)))
    hnormalizer hfibre
  filter_upwards [hprefix] with address ⟨minimumDepth, hbound⟩
  refine ⟨minimumDepth, ?_⟩
  intro depth hdepth
  simpa only [conditional_prefix_rate_identity hratio hlt depth] using hbound depth hdepth

/-- Letting the positive loss tend to zero is an order argument. The
normalizing density value may depend on the chosen loss. -/
theorem conditional_dimension_lower_of_arbitrarily_small_loss {exponent ratio : ℝ}
    (data : RootFibreData exponent) (conditional : Measure (ℕ → Bool × Bool))
    [IsProbabilityMeasure conditional]
    (hfibre : ∀ᵐ digits ∂conditional, data.root digits = ratio)
    (hprefix : ∀ loss : ℝ, 0 < loss → ∃ normalizer : ℝ, 0 < normalizer ∧
      ∀ᵐ digits ∂conditional, ∃ minimumDepth : ℕ, ∀ depth ≥ minimumDepth,
        conditional (pairedPrefix digits depth) ≤ ENNReal.ofReal
          ((4 * ratio) ^ (-(depth : ℝ)) * Real.exp (loss * depth) / normalizer)) :
    ENNReal.ofReal (Real.log (4 * ratio) / Real.log (1 / ratio)) ≤
      dimH (intersection exponent ratio) := by
  obtain ⟨digits, hdigits⟩ := hfibre.exists
  have hband : ratio ∈ Set.Icc data.lower data.upper := by
    rw [← hdigits]
    exact data.root_in_band digits
  have hquarter : 1 / 4 < ratio := data.lower_gt_quarter.trans_le hband.1
  have hratio : 0 < ratio := by linarith
  have hlt : ratio < 1 := by linarith [data.upper_lt_half, hband.2]
  have hdenominator : 0 < Real.log (1 / ratio) :=
    Real.log_pos ((one_lt_div hratio).mpr hlt)
  have hnumerator : 0 < Real.log (4 * ratio) := Real.log_pos (by linarith)
  by_cases htop : dimH (intersection exponent ratio) = ∞
  · simp only [htop, le_top]
  apply (ENNReal.ofReal_le_iff_le_toReal htop).2
  by_contra hnot
  have hgap : 0 < Real.log (4 * ratio) -
      (dimH (intersection exponent ratio)).toReal * Real.log (1 / ratio) := by
    have h := (lt_div_iff₀ hdenominator).1 (lt_of_not_ge hnot)
    linarith
  let loss : ℝ := (Real.log (4 * ratio) -
    (dimH (intersection exponent ratio)).toReal * Real.log (1 / ratio)) / 2
  have hloss : 0 < loss := by dsimp [loss]; positivity
  have hdimensionNonnegative : 0 ≤ (dimH (intersection exponent ratio)).toReal :=
    ENNReal.toReal_nonneg
  have hlossUpper : loss < Real.log (4 * ratio) := by
    dsimp [loss]
    nlinarith [mul_nonneg hdimensionNonnegative hdenominator.le]
  obtain ⟨normalizer, hnormalizer, hbound⟩ := hprefix loss hloss
  have hdimension := conditional_dimension_lower_of_prefix_bound data conditional
    hnormalizer hlossUpper hfibre hbound
  have hreal := (ENNReal.ofReal_le_iff_le_toReal htop).1 hdimension
  have h := (div_le_iff₀ hdenominator).1 hreal
  dsimp [loss] at h
  linarith

end LambdaCantor.First.Roots

#print axioms LambdaCantor.First.Roots.conditional_dimension_lower_of_prefix_bound
#print axioms LambdaCantor.First.Roots.conditional_dimension_lower_of_arbitrarily_small_loss
