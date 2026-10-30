import LambdaCantor.First.Dimension
import LambdaCantor.First.ExternalProjection
import LambdaCantor.SelfSimilarity

/-! The internal exceptional-slope argument. No external axiom is introduced
here. Geometric cover costs, separation, and collisions are explicit. -/

noncomputable section
namespace LambdaCantor.First.ExceptionalSlopes

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem hausdorffMeasure_zero_of_scaled_tail_covers
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {Index : ℕ → Type*} [∀ level, Fintype (Index level)]
    {s : Set X} {ratio constant : ℝ≥0∞}
    (hsmall : ratio < 1) (hconstant : constant ≠ ∞) (exponent : ℝ)
    (cover : (level : ℕ) → Index level → Set X)
    (hdiam : ∀ level index, Metric.ediam (cover level index) ≤ constant * ratio ^ level)
    (hcover : ∀ first, s ⊆ ⋃ level ≥ first, ⋃ index, cover level index)
    (hsum : (∑' level, ∑ index, Metric.ediam (cover level index) ^ exponent) ≠ ∞) :
    Measure.hausdorffMeasure exponent s = 0 := by
  let tailCover : (first : ℕ) → (Σ offset : ℕ, Index (offset + first)) → Set X :=
    fun first index => cover (index.1 + first) index.2
  have htaildiam : ∀ first index,
      Metric.ediam (tailCover first index) ≤ constant * ratio ^ first := by
    intro first index
    exact (hdiam _ _).trans (mul_le_mul_left'
      (pow_le_pow_of_le_one zero_le hsmall.le (Nat.le_add_left _ _)) constant)
  have htailcover : ∀ first, s ⊆ ⋃ index, tailCover first index := by
    intro first point hpoint
    rcases Set.mem_iUnion.1 (hcover first hpoint) with ⟨level, hlevel⟩
    rcases Set.mem_iUnion.1 hlevel with ⟨hafter, hindex⟩
    rcases Set.mem_iUnion.1 hindex with ⟨index, hmem⟩
    obtain ⟨offset, heq⟩ := Nat.exists_eq_add_of_le hafter
    rw [Nat.add_comm] at heq
    subst level
    exact Set.mem_iUnion.2 ⟨⟨offset, index⟩, hmem⟩
  have htends : Tendsto (fun first : ℕ => constant * ratio ^ first) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hsmall) (Or.inr hconstant))
  have hmeasure := Measure.hausdorffMeasure_le_liminf_tsum exponent s
    (fun first : ℕ => constant * ratio ^ first) htends tailCover
    (Eventually.of_forall htaildiam) (Eventually.of_forall htailcover)
  have hcost : (fun first => ∑' index, Metric.ediam (tailCover first index) ^ exponent) =
      (fun first => ∑' offset, ∑ index : Index (offset + first),
        Metric.ediam (cover (offset + first) index) ^ exponent) := by
    funext first
    simp only [tailCover, ENNReal.tsum_sigma', tsum_fintype]
  rw [hcost, (ENNReal.tendsto_sum_nat_add
    (fun level => ∑ index, Metric.ediam (cover level index) ^ exponent) hsum).liminf_eq]
    at hmeasure
  exact le_antisymm hmeasure bot_le

theorem dimH_le_of_scaled_geometric_tail_covers
    {X : Type*} [EMetricSpace X] {Index : ℕ → Type*} [∀ level, Fintype (Index level)]
    {s : Set X} {ratio constant branching : ℝ≥0∞}
    (hsmall : ratio < 1) (hconstant : constant ≠ ∞) (exponent : ℝ≥0)
    (hcard : ∀ level, (Fintype.card (Index level) : ℝ≥0∞) ≤ branching ^ level)
    (hcost : branching * ratio ^ (exponent : ℝ) < 1)
    (cover : (level : ℕ) → Index level → Set X)
    (hdiam : ∀ level index, Metric.ediam (cover level index) ≤ constant * ratio ^ level)
    (hcover : ∀ first, s ⊆ ⋃ level ≥ first, ⋃ index, cover level index) :
    dimH s ≤ exponent := by
  borelize X
  have hsum_bound : ∀ level : ℕ,
      (∑ index, Metric.ediam (cover level index) ^ (exponent : ℝ)) ≤
        constant ^ (exponent : ℝ) * (branching * ratio ^ (exponent : ℝ)) ^ level := by
    intro level
    calc
      _ ≤ ∑ _index : Index level, (constant * ratio ^ level) ^ (exponent : ℝ) :=
        Finset.sum_le_sum fun index _ => ENNReal.rpow_le_rpow (hdiam level index) exponent.2
      _ = (Fintype.card (Index level) : ℝ≥0∞) *
          (constant ^ (exponent : ℝ) * (ratio ^ (exponent : ℝ)) ^ level) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hproduct : (constant * ratio ^ level) ^ (exponent : ℝ) =
            constant ^ (exponent : ℝ) * (ratio ^ level) ^ (exponent : ℝ) := by
          simpa using! ENNReal.mul_rpow_of_nonneg constant (ratio ^ level) exponent.2
        have hpower : (ratio ^ level) ^ (exponent : ℝ) =
            (ratio ^ (exponent : ℝ)) ^ level := by
          calc
            _ = ratio ^ ((level : ℝ) * (exponent : ℝ)) := by
              simpa using! (ENNReal.rpow_natCast_mul ratio level (exponent : ℝ)).symm
            _ = ratio ^ ((exponent : ℝ) * (level : ℝ)) := by rw [mul_comm]
            _ = _ := by simpa using! ENNReal.rpow_mul_natCast ratio (exponent : ℝ) level
        rw [hproduct, hpower]
      _ ≤ branching ^ level *
          (constant ^ (exponent : ℝ) * (ratio ^ (exponent : ℝ)) ^ level) :=
        mul_le_mul_right' (hcard level) _
      _ = _ := by rw [mul_pow]; ac_rfl
  have hsum : (∑' level, ∑ index,
      Metric.ediam (cover level index) ^ (exponent : ℝ)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hsum_bound)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg exponent.2 hconstant)
      (tsum_geometric_lt_top.2 hcost).ne
  apply dimH_le_of_hausdorffMeasure_ne_top
  rw [hausdorffMeasure_zero_of_scaled_tail_covers hsmall hconstant (exponent : ℝ)
    cover hdiam hcover hsum]
  exact ENNReal.zero_ne_top

/-- A superset of the slopes failing exponential separation: for every
exponential rate, arbitrarily deep projected translations collide. -/
def frequentCollisionSlopes (point : (depth : ℕ) → Fin (4 ^ depth) → ℝ × ℝ) : Set ℝ :=
  {slope | ∀ rate : ℝ, 0 < rate → ∀ first : ℕ,
    ∃ depth, first ≤ depth ∧ ∃ left right : Fin (4 ^ depth), left ≠ right ∧
      |((point depth left).2 - (point depth right).2) -
        slope * ((point depth left).1 - (point depth right).1)| < rate ^ depth}

def collisionInterval (point : (depth : ℕ) → Fin (4 ^ depth) → ℝ × ℝ)
    (gapConstant rate : ℝ) (depth : ℕ) (pair : Fin (4 ^ depth) × Fin (4 ^ depth)) : Set ℝ :=
  Set.Ioo
    (((point depth pair.1).2 - (point depth pair.2).2) /
      ((point depth pair.1).1 - (point depth pair.2).1) - gapConstant⁻¹ * rate ^ depth)
    (((point depth pair.1).2 - (point depth pair.2).2) /
      ((point depth pair.1).1 - (point depth pair.2).1) + gapConstant⁻¹ * rate ^ depth)

theorem collisionInterval_diameter
    (point : (depth : ℕ) → Fin (4 ^ depth) → ℝ × ℝ)
    {gapConstant rate : ℝ} (hgap : 0 < gapConstant) (hrate : 0 ≤ rate)
    (depth : ℕ) (pair : Fin (4 ^ depth) × Fin (4 ^ depth)) :
    Metric.ediam (collisionInterval point gapConstant rate depth pair) ≤
      ENNReal.ofReal (2 * gapConstant⁻¹) * ENNReal.ofReal rate ^ depth := by
  unfold collisionInterval
  rw [Real.ediam_Ioo, ← ENNReal.ofReal_pow hrate,
    ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (inv_nonneg.2 hgap.le))]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  exact le_rfl

theorem frequentCollisionSlopes_tail_cover
    (point : (depth : ℕ) → Fin (4 ^ depth) → ℝ × ℝ)
    {ratio gapConstant rate : ℝ} (hratio : 0 < ratio) (hgap : 0 < gapConstant)
    (hrate : 0 < rate) (hrateSmall : rate < 1)
    (hinjective : ∀ depth, Function.Injective (point depth))
    (hhorizontal : ∀ depth (left right : Fin (4 ^ depth)),
      (point depth left).1 ≠ (point depth right).1 →
      gapConstant * ratio ^ depth ≤ |(point depth left).1 - (point depth right).1|)
    (hvertical : ∀ depth (left right : Fin (4 ^ depth)),
      (point depth left).2 ≠ (point depth right).2 →
      gapConstant * ratio ^ depth ≤ |(point depth left).2 - (point depth right).2|) :
    ∀ first, frequentCollisionSlopes point ⊆
      ⋃ depth ≥ first, ⋃ pair, collisionInterval point gapConstant rate depth pair := by
  have hdecay := tendsto_pow_atTop_nhds_zero_of_lt_one hrate.le hrateSmall
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 (hdecay.eventually (gt_mem_nhds hgap))
  intro first slope hslope
  obtain ⟨depth, hdepth, left, right, hdifferent, hcollision⟩ :=
    hslope (ratio * rate) (mul_pos hratio hrate) (max first cutoff)
  have hafter : first ≤ depth := (le_max_left _ _).trans hdepth
  have hsmall : (ratio * rate) ^ depth < gapConstant * ratio ^ depth := by
    rw [mul_pow]
    have h := mul_lt_mul_of_pos_left
      (hcutoff depth ((le_max_right _ _).trans hdepth)) (pow_pos hratio depth)
    simpa only [mul_comm] using h
  have hdifferentHorizontal : (point depth left).1 ≠ (point depth right).1 := by
    intro hequal
    have hdifferentVertical : (point depth left).2 ≠ (point depth right).2 := by
      intro hequalVertical
      exact hdifferent (hinjective depth (Prod.ext hequal hequalVertical))
    have hsep := hvertical depth left right hdifferentVertical
    rw [hequal, sub_self, mul_zero, sub_zero] at hcollision
    exact (not_lt_of_ge hsep) (hcollision.trans hsmall)
  have hwidth : (ratio * rate) ^ depth / (gapConstant * ratio ^ depth) =
      gapConstant⁻¹ * rate ^ depth := by
    rw [mul_pow]
    field_simp [ne_of_gt hgap, ne_of_gt (pow_pos hratio depth)]
  have hball := projected_collision_mem_ball
    (mul_pos hgap (pow_pos hratio depth))
    (hhorizontal depth left right hdifferentHorizontal) hcollision
  rw [hwidth, Metric.mem_ball, Real.dist_eq] at hball
  have habs := abs_lt.1 hball
  refine Set.mem_iUnion.2 ⟨depth, Set.mem_iUnion.2 ⟨hafter,
    Set.mem_iUnion.2 ⟨(left, right), ?_⟩⟩⟩
  change _ < slope ∧ slope < _
  constructor <;> linarith [habs.1, habs.2]

theorem frequentCollisionSlopes_dimension_zero
    (point : (depth : ℕ) → Fin (4 ^ depth) → ℝ × ℝ)
    {ratio gapConstant : ℝ} (hratio : 0 < ratio) (hgap : 0 < gapConstant)
    (hinjective : ∀ depth, Function.Injective (point depth))
    (hhorizontal : ∀ depth (left right : Fin (4 ^ depth)),
      (point depth left).1 ≠ (point depth right).1 →
      gapConstant * ratio ^ depth ≤ |(point depth left).1 - (point depth right).1|)
    (hvertical : ∀ depth (left right : Fin (4 ^ depth)),
      (point depth left).2 ≠ (point depth right).2 →
      gapConstant * ratio ^ depth ≤ |(point depth left).2 - (point depth right).2|) :
    dimH (frequentCollisionSlopes point) = 0 := by
  apply le_antisymm ?_ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro exponent hpositive _
  have hpositiveReal : 0 < (exponent : ℝ) := hpositive
  obtain ⟨rate, hrate, hrateSmall, hcostReal⟩ :=
    exists_collision_rate (ratio := 1) zero_lt_one hpositiveReal
  simp only [div_one] at hcostReal
  have hcost : (16 : ℝ≥0∞) * ENNReal.ofReal rate ^ (exponent : ℝ) < 1 := by
    have hpower : ENNReal.ofReal rate ^ (exponent : ℝ) =
        ENNReal.ofReal (rate ^ (exponent : ℝ)) := by
      simpa using! ENNReal.ofReal_rpow_of_nonneg hrate.le exponent.2
    rw [hpower]
    have heq : (16 : ℝ≥0∞) * ENNReal.ofReal (rate ^ (exponent : ℝ)) =
        ENNReal.ofReal (16 * rate ^ (exponent : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [heq]
    exact ENNReal.ofReal_lt_one.2 hcostReal
  have hcard : ∀ depth : ℕ,
      (Fintype.card (Fin (4 ^ depth) × Fin (4 ^ depth)) : ℝ≥0∞) ≤ (16 : ℝ≥0∞) ^ depth := by
    intro depth
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    rw [← mul_pow]
    norm_num
  have hdimension := dimH_le_of_scaled_geometric_tail_covers
    (ENNReal.ofReal_lt_one.2 hrateSmall) ENNReal.ofReal_ne_top exponent hcard hcost
    (collisionInterval point gapConstant rate)
    (collisionInterval_diameter point hgap hrate.le)
    (frequentCollisionSlopes_tail_cover point hratio hgap hrate hrateSmall
      hinjective hhorizontal hvertical)
  simpa only [zero_add] using hdimension

end LambdaCantor.First.ExceptionalSlopes
