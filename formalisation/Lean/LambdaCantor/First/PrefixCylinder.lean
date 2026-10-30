import LambdaCantor.First.ProjectionMeasure

noncomputable section
namespace LambdaCantor.First.PrefixSlopes

open Set MeasureTheory
open scoped ENNReal NNReal

def prefixCylinder {depth : ℕ} (word : Fin depth → Bool × Bool) : Set (ℕ → Bool × Bool) :=
  {digits | ∀ position : Fin depth, digits position = word position}

theorem prefixCylinder_measurable {depth : ℕ} (word : Fin depth → Bool × Bool) :
    MeasurableSet (prefixCylinder word) := by
  have hequal : prefixCylinder word = ⋂ position : Fin depth,
      {digits : ℕ → Bool × Bool | digits position = word position} := by
    ext digits
    simp [prefixCylinder]
  rw [hequal]
  exact MeasurableSet.iInter fun position =>
    measurableSet_eq_fun (measurable_pi_apply (position : ℕ)) measurable_const

theorem prefixCylinder_disjoint {depth : ℕ} {left right : Fin depth → Bool × Bool}
    (hdifferent : left ≠ right) : Disjoint (prefixCylinder left) (prefixCylinder right) := by
  rw [Set.disjoint_left]
  intro digits hleft hright
  apply hdifferent
  funext position
  exact (hleft position).symm.trans (hright position)

theorem prefixCylinder_mass {depth : ℕ} (word : Fin depth → Bool × Bool) :
    Roots.pairedAddressMeasure (prefixCylinder word) = (1 / 4 : ℝ≥0∞) ^ depth := by
  let digits : ℕ → Bool × Bool := fun position =>
    (extendWord (fun j => (word j).1) position, extendWord (fun j => (word j).2) position)
  have hequal : prefixCylinder word = Roots.pairedPrefix digits depth := by
    ext other
    constructor
    · intro h position hposition
      simpa [digits, extendWord, hposition] using h ⟨position, hposition⟩
    · intro h position
      simpa [digits, extendWord, position.isLt] using h position position.isLt
  rw [hequal, Roots.pairedPrefix_mass]

theorem address_close_of_prefix {ratio : ℝ} (hratio : 0 ≤ ratio) (hcontract : ratio < 1)
    {depth : ℕ} {left right : ℕ → Bool} (hagrees : ∀ position < depth, left position = right position) :
    |address ratio left - address ratio right| ≤ ratio ^ depth := by
  have hprefix : prefixValue ratio left depth = prefixValue ratio right depth := by
    unfold prefixValue
    congr 1
    apply Finset.sum_congr rfl
    intro position hposition
    rw [hagrees position (Finset.mem_range.1 hposition)]
  rw [address_prefix_tail hratio hcontract left depth,
    address_prefix_tail hratio hcontract right depth, hprefix]
  have hleft0 := address_nonnegative hratio hcontract (fun position => left (position + depth))
  have hleft1 := address_le_one hratio hcontract (fun position => left (position + depth))
  have hright0 := address_nonnegative hratio hcontract (fun position => right (position + depth))
  have hright1 := address_le_one hratio hcontract (fun position => right (position + depth))
  apply abs_le.2
  constructor <;> nlinarith [pow_nonneg hratio depth]

theorem projectedAddress_close_of_prefix {ratio slope : ℝ} (hratio : 0 ≤ ratio)
    (hcontract : ratio < 1) {depth : ℕ} {word : Fin depth → Bool × Bool}
    {left right : ℕ → Bool × Bool} (hleft : left ∈ prefixCylinder word)
    (hright : right ∈ prefixCylinder word) :
    |projectedAddress ratio slope left - projectedAddress ratio slope right| ≤
      (|slope| + 1) * ratio ^ depth := by
  have hsame : ∀ position < depth, left position = right position := by
    intro position hposition
    exact (hleft ⟨position, hposition⟩).trans (hright ⟨position, hposition⟩).symm
  have hx := address_close_of_prefix hratio hcontract
    (fun position hposition => congrArg Prod.fst (hsame position hposition))
  have hy := address_close_of_prefix hratio hcontract
    (fun position hposition => congrArg Prod.snd (hsame position hposition))
  unfold projectedAddress
  calc
    _ = |(address ratio (fun position => (left position).2) -
        address ratio (fun position => (right position).2)) -
        slope * (address ratio (fun position => (left position).1) -
          address ratio (fun position => (right position).1))| := by congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ ratio ^ depth + |slope| * ratio ^ depth := by
      rw [abs_mul]
      exact add_le_add hy (mul_le_mul_of_nonneg_left hx (abs_nonneg slope))
    _ = _ := by ring

/-- The paper's strip-count estimate in its mass-weighted form, for actual
Cantor cylinders and the actual projected probability law. -/
theorem prefix_strip_count {ratio slope center width constant exponent : ℝ}
    (hratio : 0 < ratio) (hcontract : ratio < 1) (hwidth : 0 ≤ width)
    (hball : ∀ center radius : ℝ, 0 < radius →
      projectedMeasure ratio slope (Metric.ball center radius) ≤
        ENNReal.ofReal (constant * radius ^ exponent))
    {depth : ℕ} (selected : Finset (Fin depth → Bool × Bool))
    (hmeets : ∀ word ∈ selected, ∃ digits ∈ prefixCylinder word,
      |projectedAddress ratio slope digits - center| ≤ width) :
    (selected.card : ℝ≥0∞) * (1 / 4 : ℝ≥0∞) ^ depth ≤
      ENNReal.ofReal (constant *
        (width + (|slope| + 2) * ratio ^ depth) ^ exponent) := by
  let radius := width + (|slope| + 2) * ratio ^ depth
  have hpositive : 0 < radius := by
    dsimp [radius]
    positivity
  apply cylinder_count_from_mass Roots.pairedAddressMeasure selected prefixCylinder
    (projectedAddress ratio slope ⁻¹' Metric.ball center radius)
    ((1 / 4 : ℝ≥0∞) ^ depth)
  · intro left _ right _ hdifferent
    exact prefixCylinder_disjoint hdifferent
  · intro word _
    exact prefixCylinder_measurable word
  · intro word _
    exact (prefixCylinder_mass word).ge
  · intro word hword digits hdigits
    obtain ⟨witness, hwitness, hstrip⟩ := hmeets word hword
    change projectedAddress ratio slope digits ∈ Metric.ball center radius
    rw [Metric.mem_ball, Real.dist_eq]
    have hclose := projectedAddress_close_of_prefix (slope := slope)
      hratio.le hcontract hdigits hwitness
    have htriangle := abs_add_le
      (projectedAddress ratio slope digits - projectedAddress ratio slope witness)
      (projectedAddress ratio slope witness - center)
    have hpositivePower := pow_pos hratio depth
    dsimp [radius]
    have hsum : |projectedAddress ratio slope digits - center| ≤
        (|slope| + 1) * ratio ^ depth + width := by
      calc
        _ = |(projectedAddress ratio slope digits - projectedAddress ratio slope witness) +
          (projectedAddress ratio slope witness - center)| := by congr 1; ring
        _ ≤ _ := htriangle
        _ ≤ _ := add_le_add hclose hstrip
    nlinarith
  · rw [← Measure.map_apply (projectedAddress_measurable hratio.le hcontract)
      Metric.isOpen_ball.measurableSet]
    exact hball center radius hpositive

end LambdaCantor.First.PrefixSlopes
