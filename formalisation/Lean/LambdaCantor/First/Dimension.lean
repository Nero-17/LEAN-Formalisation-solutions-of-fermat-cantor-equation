import LambdaCantor.Common
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import LambdaCantor.Curve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Elementary and dimensional components of Section 2, Theorem `dimension-upper`
and Corollary `first-lower`. No unproved paper result is asserted here. -/
namespace LambdaCantor.First

open Set MeasureTheory
open scoped ENNReal NNReal

/-- The real-valued upper bound printed in Theorem `dimension-upper`. -/
noncomputable def dimensionUpperBound (ratio : ℝ) : ℝ :=
  max (2 * Real.log 2 / Real.log (1 / ratio) - 1) 0

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring

lemma log_reciprocal_pos {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    0 < Real.log (1 / ratio) := by
  apply Real.log_pos
  exact (lt_div_iff₀ hpos).2 (by simpa using hlt)

lemma dimensionUpperBound_nonneg (ratio : ℝ) : 0 ≤ dimensionUpperBound ratio :=
  le_max_right _ _

lemma dimensionUpperBound_eq_zero {ratio : ℝ} (hpos : 0 < ratio)
    (hquarter : ratio ≤ 1 / 4) : dimensionUpperBound ratio = 0 := by
  have hlog : 2 * Real.log 2 ≤ Real.log (1 / ratio) := by
    rw [← log_four]
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ hpos).2 (by linarith)
  have hden : 0 < Real.log (1 / ratio) :=
    log_reciprocal_pos hpos (by linarith)
  unfold dimensionUpperBound
  exact max_eq_right ((sub_nonpos).2 ((div_le_one hden).2 hlog))

lemma dimensionUpperBound_half : dimensionUpperBound (1 / 2) = 1 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [dimensionUpperBound, mul_div_cancel_right₀, hlog]

/-- The endpoint case of Theorem `dimension-upper`, without any separation input. -/
theorem dimension_upper_half {exponent : ℝ} (hexponent : 1 < exponent) :
    dimH (intersection exponent (1 / 2)) ≤
      ENNReal.ofReal (dimensionUpperBound (1 / 2)) := by
  rw [dimensionUpperBound_half, ENNReal.ofReal_one,
    dimH_intersection_half (by linarith : 0 < exponent)]

lemma dimensionUpperBound_pos {ratio : ℝ} (hquarter : 1 / 4 < ratio)
    (hlt : ratio < 1) : 0 < dimensionUpperBound ratio := by
  have hpos : 0 < ratio := by linarith
  have hlog : Real.log (1 / ratio) < 2 * Real.log 2 := by
    rw [← log_four]
    apply Real.log_lt_log (div_pos (by norm_num) hpos)
    exact (div_lt_iff₀ hpos).2 (by linarith)
  have hden := log_reciprocal_pos hpos hlt
  exact lt_of_lt_of_le (sub_pos.2 ((one_lt_div hden).2 hlog)) (le_max_left _ _)

lemma dimH_eq_zero_of_dimensionUpperBound {X : Type*} [EMetricSpace X]
    {s : Set X} {ratio : ℝ} (hpos : 0 < ratio) (hquarter : ratio ≤ 1 / 4)
    (hbound : dimH s ≤ ENNReal.ofReal (dimensionUpperBound ratio)) : dimH s = 0 := by
  rw [dimensionUpperBound_eq_zero hpos hquarter, ENNReal.ofReal_zero] at hbound
  exact le_antisymm hbound bot_le

/-- Removing a countable set of points preserves an upper dimension bound. -/
lemma dimH_le_of_diff_countable {X : Type*} [EMetricSpace X]
    {s exceptional : Set X} {bound : ℝ≥0∞} (hcount : exceptional.Countable)
    (hbound : dimH (s \ exceptional) ≤ bound) : dimH s ≤ bound := by
  have hcover : s ⊆ (s \ exceptional) ∪ exceptional := by
    intro x hx
    by_cases he : x ∈ exceptional
    · exact Or.inr he
    · exact Or.inl ⟨hx, he⟩
  apply (dimH_mono hcover).trans
  rw [dimH_union, hcount.dimH_zero]
  exact max_le hbound zero_le

/-! The following covering result is the analytic end of the block-iteration
argument. The hypotheses contain concrete covers, not a desired dimension bound. -/

open Filter Topology

/-- Local dimension estimates patch without requiring an explicit countable
choice of neighborhoods; second countability supplies that reduction. -/
theorem dimH_le_of_local_bounds {X : Type*} [EMetricSpace X]
    [SecondCountableTopology X] {s : Set X} {bound : ℝ≥0∞}
    (hlocal : ∀ point ∈ s, ∃ neighborhood ∈ 𝓝[s] point,
      dimH neighborhood ≤ bound) : dimH s ≤ bound := by
  by_contra h
  rcases exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (lt_of_not_ge h) with
    ⟨point, hpoint, hall⟩
  rcases hlocal point hpoint with ⟨neighborhood, hneighborhood, hbound⟩
  exact (hall neighborhood hneighborhood).not_ge hbound

/-- A zero-dimensional exceptional set does not affect any upper bound. -/
theorem dimH_le_of_exceptional_set {X : Type*} [EMetricSpace X]
    {s exceptional : Set X} {bound : ℝ≥0∞} (hzero : dimH exceptional = 0)
    (hregular : dimH (s \ exceptional) ≤ bound) : dimH s ≤ bound := by
  have hcover : s ⊆ (s \ exceptional) ∪ exceptional := by
    intro point hpoint
    by_cases hexceptional : point ∈ exceptional
    · exact Or.inr hexceptional
    · exact Or.inl ⟨hpoint, hexceptional⟩
  apply (dimH_mono hcover).trans
  rw [dimH_union, hzero]
  exact max_le hregular zero_le

/-- A map whose restrictions to neighborhoods have Lipschitz inverses cannot
increase dimension under preimage. The neighborhood cover need not be given
in advance: second countability enters through local-to-global dimension. -/
theorem dimH_preimage_le_of_locally_antilipschitz
    {X Y : Type*} [EMetricSpace X] [EMetricSpace Y] [SecondCountableTopology X]
    {domain : Set X} {exceptional : Set Y} {f : X → Y}
    (hlocal : ∀ point ∈ domain, ∃ (constant : ℝ≥0) (neighborhood : Set X),
      neighborhood ∈ 𝓝[domain] point ∧
      AntilipschitzWith constant (fun point : neighborhood => f point)) :
    dimH (domain ∩ f ⁻¹' exceptional) ≤ dimH exceptional := by
  apply dimH_le_of_local_bounds
  intro point hpoint
  rcases hlocal point hpoint.1 with ⟨constant, neighborhood, hneighborhood, hinverse⟩
  refine ⟨neighborhood ∩ (domain ∩ f ⁻¹' exceptional),
    inter_mem ((nhdsWithin_mono point inter_subset_left) hneighborhood)
      self_mem_nhdsWithin, ?_⟩
  have himage : (Subtype.val : neighborhood → X) ''
      (Subtype.val ⁻¹' (domain ∩ f ⁻¹' exceptional)) =
        neighborhood ∩ (domain ∩ f ⁻¹' exceptional) := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe, inter_comm]
  have hsubset : (fun point : neighborhood => f point) ''
      (Subtype.val ⁻¹' (domain ∩ f ⁻¹' exceptional)) ⊆ exceptional := by
    rintro value ⟨point, hpoint, rfl⟩
    exact hpoint.2
  have hdimension := isometry_subtype_coe.dimH_image
    (Subtype.val ⁻¹' (domain ∩ f ⁻¹' exceptional) : Set neighborhood)
  rw [himage] at hdimension
  exact hdimension.le.trans ((hinverse.le_dimH_image _).trans (dimH_mono hsubset))

theorem exceptional_curve_dimension_zero {exponent : ℝ} (hexponent : 0 < exponent)
    {tangent : ℝ → ℝ} {exceptional : Set ℝ} (hzero : dimH exceptional = 0)
    (hlocal : ∀ point ∈ Set.Ioo (0 : ℝ) 1,
      ∃ (constant : ℝ≥0) (neighborhood : Set ℝ),
        neighborhood ∈ 𝓝[Set.Ioo (0 : ℝ) 1] point ∧
        AntilipschitzWith constant (fun point : neighborhood => tangent point)) :
    dimH (curvePoint exponent '' (Set.Ioo (0 : ℝ) 1 ∩ tangent ⁻¹' exceptional)) = 0 := by
  apply le_antisymm ?_ zero_le
  have hpreimage := dimH_preimage_le_of_locally_antilipschitz
    (exceptional := exceptional) hlocal
  rw [hzero] at hpreimage
  exact ((contDiffOn_curvePoint hexponent).dimH_image_le
    (convex_Ioo (0 : ℝ) 1) inter_subset_left).trans hpreimage

/-- Counting cylinders from their disjoint masses. Applying this to the set of
cylinders meeting a strip and a containing wider strip gives the mass-to-count
step, with no assertion that the required self-similar masses already exist. -/
theorem cylinder_count_from_mass {X ι : Type*} [MeasurableSpace X]
    (measure : Measure X) (selected : Finset ι) (cylinder : ι → Set X)
    (region : Set X) (mass bound : ℝ≥0∞)
    (hdisjoint : PairwiseDisjoint (↑selected) cylinder)
    (hmeasurable : ∀ index ∈ selected, MeasurableSet (cylinder index))
    (hmass : ∀ index ∈ selected, mass ≤ measure (cylinder index))
    (hsubset : ∀ index ∈ selected, cylinder index ⊆ region)
    (hbound : measure region ≤ bound) : (selected.card : ℝ≥0∞) * mass ≤ bound := by
  calc
    _ = ∑ _index ∈ selected, mass := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ index ∈ selected, measure (cylinder index) := Finset.sum_le_sum hmass
    _ = measure (⋃ index ∈ selected, cylinder index) :=
      (measure_biUnion_finset hdisjoint hmeasurable).symm
    _ ≤ measure region := measure_mono (iUnion₂_subset hsubset)
    _ ≤ bound := hbound

/-- Geometric finite covers give zero Hausdorff measure whenever branching times
the diameter contraction to the given power is less than one. -/
theorem hausdorffMeasure_zero_of_geometric_covers
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} {ratio : ℝ≥0∞} (hsmall : ratio < 1) (branching : ℕ)
    (exponent : ℝ≥0) (hcost : (branching : ℝ≥0∞) * ratio ^ (exponent : ℝ) < 1)
    (cover : (level : ℕ) → Fin (branching ^ level) → Set X)
    (hdiam : ∀ level index, Metric.ediam (cover level index) ≤ ratio ^ level)
    (hcover : ∀ level, s ⊆ ⋃ index, cover level index) :
    Measure.hausdorffMeasure (exponent : ℝ) s = 0 := by
  apply le_antisymm ?_ bot_le
  have hmeasure := Measure.hausdorffMeasure_le_liminf_sum (exponent : ℝ) s
    (fun level : ℕ => ratio ^ level)
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hsmall) cover
    (Eventually.of_forall hdiam) (Eventually.of_forall hcover)
  have hsum : ∀ level : ℕ,
      (∑ index, Metric.ediam (cover level index) ^ (exponent : ℝ)) ≤
        ((branching : ℝ≥0∞) * ratio ^ (exponent : ℝ)) ^ level := by
    intro level
    calc
      _ ≤ ∑ _index : Fin (branching ^ level),
          (ratio ^ level) ^ (exponent : ℝ) :=
        Finset.sum_le_sum fun index _ => ENNReal.rpow_le_rpow (hdiam level index) exponent.2
      _ = (branching : ℝ≥0∞) ^ level * (ratio ^ (exponent : ℝ)) ^ level := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow]
        rw [← ENNReal.rpow_natCast_mul, mul_comm (level : ℝ), ENNReal.rpow_mul_natCast]
      _ = _ := (mul_pow _ _ _).symm
  calc
    _ ≤ liminf (fun level : ℕ =>
        ∑ index, Metric.ediam (cover level index) ^ (exponent : ℝ)) atTop := hmeasure
    _ ≤ liminf (fun level : ℕ =>
        ((branching : ℝ≥0∞) * ratio ^ (exponent : ℝ)) ^ level) atTop :=
      liminf_le_liminf (Eventually.of_forall hsum)
    _ = 0 := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hcost).liminf_eq

theorem dimH_le_of_geometric_covers
    {X : Type*} [EMetricSpace X] {s : Set X} {ratio : ℝ≥0∞}
    (hsmall : ratio < 1) (branching : ℕ) (exponent : ℝ≥0)
    (hcost : (branching : ℝ≥0∞) * ratio ^ (exponent : ℝ) < 1)
    (cover : (level : ℕ) → Fin (branching ^ level) → Set X)
    (hdiam : ∀ level index, Metric.ediam (cover level index) ≤ ratio ^ level)
    (hcover : ∀ level, s ⊆ ⋃ index, cover level index) : dimH s ≤ exponent := by
  borelize X
  apply dimH_le_of_hausdorffMeasure_ne_top
  rw [hausdorffMeasure_zero_of_geometric_covers hsmall branching exponent hcost cover hdiam hcover]
  exact ENNReal.zero_ne_top

/-- Taking exponents down to a target bound, with explicit finite covers at each
exponent. This closes the limiting step of a block-counting proof. -/
theorem dimH_le_of_geometric_covers_above
    {X : Type*} [EMetricSpace X] {s : Set X} {bound : ℝ≥0∞}
    (hcovers : ∀ exponent : ℝ≥0, bound < exponent →
      ∃ (ratio : ℝ≥0∞) (branching : ℕ)
        (cover : (level : ℕ) → Fin (branching ^ level) → Set X),
        ratio < 1 ∧ (branching : ℝ≥0∞) * ratio ^ (exponent : ℝ) < 1 ∧
        (∀ level index, Metric.ediam (cover level index) ≤ ratio ^ level) ∧
        (∀ level, s ⊆ ⋃ index, cover level index)) : dimH s ≤ bound := by
  borelize X
  apply dimH_le
  intro exponent hinfinite
  by_contra hle
  rcases hcovers exponent (lt_of_not_ge hle) with
    ⟨ratio, branching, cover, hsmall, hcost, hdiam, hcover⟩
  have hzero := hausdorffMeasure_zero_of_geometric_covers hsmall branching exponent
    hcost cover hdiam hcover
  rw [hzero] at hinfinite
  exact ENNReal.zero_ne_top hinfinite

/-- Hausdorff--Cantelli in the level-indexed form needed for exceptional slopes.
The set is covered by every tail of the finite interval families. Summability of
the diameter costs, rather than a measure estimate on individual intervals,
forces its Hausdorff measure to vanish. -/
theorem hausdorffMeasure_zero_of_tail_covers
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} {ratio : ℝ≥0∞} (hsmall : ratio < 1) (exponent : ℝ)
    (count : ℕ → ℕ) (cover : (level : ℕ) → Fin (count level) → Set X)
    (hdiam : ∀ level index, Metric.ediam (cover level index) ≤ ratio ^ level)
    (hcover : ∀ first, s ⊆ ⋃ level ≥ first, ⋃ index, cover level index)
    (hsum : (∑' level, ∑ index,
      Metric.ediam (cover level index) ^ exponent) ≠ ∞) :
    Measure.hausdorffMeasure exponent s = 0 := by
  let tailCover : (first : ℕ) → (Σ offset : ℕ, Fin (count (offset + first))) → Set X :=
    fun first index => cover (index.1 + first) index.2
  have htaildiam : ∀ first index, Metric.ediam (tailCover first index) ≤ ratio ^ first := by
    intro first index
    exact (hdiam _ _).trans
      (pow_le_pow_of_le_one zero_le hsmall.le (Nat.le_add_left _ _))
  have htailcover : ∀ first, s ⊆ ⋃ index, tailCover first index := by
    intro first point hpoint
    rcases Set.mem_iUnion.1 (hcover first hpoint) with ⟨level, hlevel⟩
    rcases Set.mem_iUnion.1 hlevel with ⟨hafter, hindex⟩
    rcases Set.mem_iUnion.1 hindex with ⟨index, hmem⟩
    obtain ⟨offset, heq⟩ := Nat.exists_eq_add_of_le hafter
    rw [Nat.add_comm] at heq
    subst level
    exact Set.mem_iUnion.2 ⟨⟨offset, index⟩, hmem⟩
  have hmeasure := Measure.hausdorffMeasure_le_liminf_tsum exponent s
    (fun first : ℕ => ratio ^ first)
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hsmall) tailCover
    (Eventually.of_forall htaildiam) (Eventually.of_forall htailcover)
  have hcost : (fun first => ∑' index, Metric.ediam (tailCover first index) ^ exponent) =
      (fun first => ∑' offset, ∑ index : Fin (count (offset + first)),
        Metric.ediam (cover (offset + first) index) ^ exponent) := by
    funext first
    simp only [tailCover, ENNReal.tsum_sigma', tsum_fintype]
  rw [hcost, (ENNReal.tendsto_sum_nat_add
    (fun level => ∑ index, Metric.ediam (cover level index) ^ exponent) hsum).liminf_eq]
    at hmeasure
  exact le_antisymm hmeasure bot_le

/-- Exponentially many intervals with geometrically small diameter have the
expected limsup dimension bound. The `branching = 16` case is the pair count
used for exceptional projection slopes. -/
theorem dimH_le_of_geometric_tail_covers
    {X : Type*} [EMetricSpace X] {s : Set X} {ratio : ℝ≥0∞}
    (hsmall : ratio < 1) (branching : ℕ) (exponent : ℝ≥0)
    (hcost : (branching : ℝ≥0∞) * ratio ^ (exponent : ℝ) < 1)
    (cover : (level : ℕ) → Fin (branching ^ level) → Set X)
    (hdiam : ∀ level index, Metric.ediam (cover level index) ≤ ratio ^ level)
    (hcover : ∀ first, s ⊆ ⋃ level ≥ first, ⋃ index, cover level index) :
    dimH s ≤ exponent := by
  borelize X
  have hsum : (∑' level, ∑ index,
      Metric.ediam (cover level index) ^ (exponent : ℝ)) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun level : ℕ =>
      ((branching : ℝ≥0∞) * ratio ^ (exponent : ℝ)) ^ level) ?_)
      (tsum_geometric_lt_top.2 hcost)
    intro level
    calc
      _ ≤ ∑ _index : Fin (branching ^ level), (ratio ^ level) ^ (exponent : ℝ) :=
        Finset.sum_le_sum fun index _ => ENNReal.rpow_le_rpow (hdiam level index) exponent.2
      _ = (branching : ℝ≥0∞) ^ level * (ratio ^ (exponent : ℝ)) ^ level := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        rw [← ENNReal.rpow_natCast_mul, mul_comm (level : ℝ), ENNReal.rpow_mul_natCast]
      _ = _ := (mul_pow _ _ _).symm
  apply dimH_le_of_hausdorffMeasure_ne_top
  rw [hausdorffMeasure_zero_of_tail_covers hsmall (exponent : ℝ)
    (fun level => branching ^ level) cover hdiam hcover hsum]
  exact ENNReal.zero_ne_top

/-- The zero-dimensional parameter interval implies `first-lower`. Nonemptiness
of the positive-dimensional set is independently supplied by the half-ratio case. -/
theorem first_lower_of_dimension_zero {exponent : ℝ} (hexponent : 1 < exponent)
    (hzero : ∀ ratio : ℝ, 0 < ratio → ratio ≤ 1 / 4 →
      dimH (intersection exponent ratio) = 0) : 1 / 4 ≤ firstTransition exponent := by
  apply le_csInf
  · exact ⟨1 / 2, ⟨by norm_num,
      positive_dimH_intersection_half (by linarith)⟩⟩
  · intro ratio hratio
    by_contra hlt
    have hsmall : ratio ≤ 1 / 4 := le_of_lt (lt_of_not_ge hlt)
    have h := hzero ratio hratio.1.1 hsmall
    exact (ne_of_gt hratio.2) h

theorem first_lower_of_dimension_upper {exponent : ℝ} (hexponent : 1 < exponent)
    (hupper : ∀ ratio : ℝ, 0 < ratio → ratio ≤ 1 / 2 →
      dimH (intersection exponent ratio) ≤ ENNReal.ofReal (dimensionUpperBound ratio)) :
    1 / 4 ≤ firstTransition exponent := by
  apply first_lower_of_dimension_zero hexponent
  intro ratio hpos hquarter
  exact dimH_eq_zero_of_dimensionUpperBound hpos hquarter
    (hupper ratio hpos (by linarith))

/-- A collision of two projections excludes only an interval about their
secant slope. This is the elementary transversality estimate in the first
paragraph of the dimension proof. -/
theorem projected_collision_slope_bound {horizontal vertical slope radius : ℝ}
    (hhorizontal : horizontal ≠ 0)
    (hcollision : |vertical - slope * horizontal| < radius) :
    |slope - vertical / horizontal| < radius / |horizontal| := by
  have heq : slope - vertical / horizontal =
      -(vertical - slope * horizontal) / horizontal := by
    field_simp
    ring
  rw [heq, abs_div, abs_neg]
  exact (div_lt_div_iff_of_pos_right (abs_pos.2 hhorizontal)).2 hcollision

/-- Every point of a square meeting a narrow strip lies in its controlled
enlargement. This justifies using the full cylinder mass in the strip count. -/
theorem square_meeting_strip_subset {point witness : ℝ × ℝ}
    {slope intercept side width : ℝ}
    (hhorizontal : |point.1 - witness.1| ≤ side)
    (hvertical : |point.2 - witness.2| ≤ side)
    (hmeets : |witness.2 - slope * witness.1 - intercept| ≤ width) :
    |point.2 - slope * point.1 - intercept| ≤ (|slope| + 1) * side + width := by
  calc
    _ = |((point.2 - witness.2) - slope * (point.1 - witness.1)) +
        (witness.2 - slope * witness.1 - intercept)| := by congr 1 <;> ring
    _ ≤ |(point.2 - witness.2) - slope * (point.1 - witness.1)| +
        |witness.2 - slope * witness.1 - intercept| := abs_add_le _ _
    _ ≤ (|point.2 - witness.2| + |slope * (point.1 - witness.1)|) + width :=
      add_le_add (abs_sub _ _) hmeets
    _ ≤ (|slope| + 1) * side + width := by
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hhorizontal (abs_nonneg slope)]

/-- Derivative control puts the graph in a strip parallel to the fixed slope.
Unlike a tangent-line estimate at one point, this holds between every pair of
points in the convex neighborhood and can be reused inside each parent square. -/
theorem graph_strip_of_derivative_close {f derivative : ℝ → ℝ}
    {domain : Set ℝ} {slope tolerance x y : ℝ} (hconvex : Convex ℝ domain)
    (hderivative : ∀ point ∈ domain, HasDerivWithinAt f (derivative point) domain point)
    (hclose : ∀ point ∈ domain, |derivative point - slope| ≤ tolerance)
    (hx : x ∈ domain) (hy : y ∈ domain) :
    |(f y - slope * y) - (f x - slope * x)| ≤ tolerance * |y - x| := by
  have hsub : ∀ point ∈ domain,
      HasDerivWithinAt (fun value => f value - slope * value)
        (derivative point - slope) domain point := by
    intro point hpoint
    simpa only [mul_one] using! (hderivative point hpoint).sub
      (((hasDerivAt_id point).const_mul slope).hasDerivWithinAt)
  simpa only [Real.norm_eq_abs] using
    hconvex.norm_image_sub_le_of_norm_hasDerivWithin_le hsub
      (fun point hpoint => by simpa only [Real.norm_eq_abs] using hclose point hpoint) hx hy

theorem graph_strip_in_parent {f derivative : ℝ → ℝ}
    {domain : Set ℝ} {slope ratio x y : ℝ} (hconvex : Convex ℝ domain)
    (hratio : 0 ≤ ratio) (block parent : ℕ)
    (hderivative : ∀ point ∈ domain, HasDerivWithinAt f (derivative point) domain point)
    (hclose : ∀ point ∈ domain, |derivative point - slope| ≤ ratio ^ block)
    (hx : x ∈ domain) (hy : y ∈ domain) (hwidth : |y - x| ≤ ratio ^ parent) :
    |(f y - slope * y) - (f x - slope * x)| ≤ ratio ^ (parent + block) := by
  apply (graph_strip_of_derivative_close hconvex hderivative hclose hx hy).trans
  calc
    ratio ^ block * |y - x| ≤ ratio ^ block * ratio ^ parent :=
      mul_le_mul_of_nonneg_left hwidth (pow_nonneg hratio _)
    _ = ratio ^ (parent + block) := by rw [pow_add, mul_comm]

theorem projected_collision_mem_ball {horizontal vertical slope radius gap : ℝ}
    (hgap : 0 < gap) (hseparation : gap ≤ |horizontal|)
    (hcollision : |vertical - slope * horizontal| < radius) :
    slope ∈ Metric.ball (vertical / horizontal) (radius / gap) := by
  have habs : 0 < |horizontal| := hgap.trans_le hseparation
  have hradius : 0 < radius := (abs_nonneg _).trans_lt hcollision
  rw [Metric.mem_ball, Real.dist_eq]
  exact (projected_collision_slope_bound (abs_pos.1 habs) hcollision).trans_le
    (div_le_div_of_nonneg_left hradius.le hgap hseparation)

theorem no_projected_collision_of_same_horizontal
    {vertical slope radius gap : ℝ} (hseparation : gap ≤ |vertical|)
    (hsmall : radius ≤ gap) : ¬ |vertical - slope * 0| < radius := by
  simpa using not_lt_of_ge (hsmall.trans hseparation)

/-- Every positive Hausdorff exponent permits an exponential exclusion rate
whose costs beat the `16^level` pair count. -/
theorem exists_collision_rate {ratio exponent : ℝ} (hratio : 0 < ratio)
    (hexponent : 0 < exponent) :
    ∃ rate : ℝ, 0 < rate ∧ rate < ratio ∧ 16 * (rate / ratio) ^ exponent < 1 := by
  refine ⟨ratio * (1 / 32 : ℝ) ^ exponent⁻¹, ?_, ?_, ?_⟩
  · exact mul_pos hratio (Real.rpow_pos_of_pos (by norm_num) _)
  · exact (mul_lt_iff_lt_one_right hratio).2
      (Real.rpow_lt_one (by norm_num) (by norm_num) (inv_pos.2 hexponent))
  · rw [mul_div_cancel_left₀ _ (ne_of_gt hratio),
      Real.rpow_inv_rpow (by norm_num) (ne_of_gt hexponent)]
    norm_num

end LambdaCantor.First

