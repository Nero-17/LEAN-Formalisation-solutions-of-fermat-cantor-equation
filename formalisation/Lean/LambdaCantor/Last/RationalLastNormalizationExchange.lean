import LambdaCantor.Last.RationalLastNormalizationFermat

noncomputable section
namespace LambdaCantor.Last

/-- Swap coordinates and take one additional prefix in the old second
coordinate. This realizes the phase change r ↦ 1/(λr) on actual dust. -/
def prefixExchangeMap (ratio : ℝ) (digit : Bool) (point : ℝ × ℝ) : ℝ × ℝ :=
  (point.2, scalarWordMap ratio [digit] point.1)

def exchangedNormalizedFunction (ratio slope : ℝ) (digit : Bool)
    (function : (ℝ × ℝ) → ℝ) (point : ℝ × ℝ) : ℝ :=
  function (prefixExchangeMap ratio digit point)/(ratio*slope)

theorem prefixExchangeMap_contDiff (ratio : ℝ) (digit : Bool) :
    ContDiff ℝ 2 (prefixExchangeMap ratio digit) := by
  unfold prefixExchangeMap
  simp only [scalarWordMap]
  fun_prop

theorem prefixExchangeMap_injective {ratio : ℝ} (positive : 0 < ratio) (digit : Bool) :
    Function.Injective (prefixExchangeMap ratio digit) := by
  intro first second equal
  apply Prod.ext
  · have coordinates := congrArg Prod.snd equal
    change (if digit then 1-ratio else 0)+ratio*first.1 =
      (if digit then 1-ratio else 0)+ratio*second.1 at coordinates
    exact mul_left_cancel₀ positive.ne' (add_left_cancel coordinates)
  · exact congrArg Prod.fst equal

theorem prefixExchangeMap_mem_dust {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (digit : Bool) {point : ℝ × ℝ} (membership : point ∈ cantorDust ratio) :
    prefixExchangeMap ratio digit point ∈ cantorDust ratio :=
  ⟨membership.2, scalarWordMap_mem_cantorSet nonnegative less_one [digit] membership.1⟩

theorem exists_prefixExchange_preimage {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    {point : ℝ × ℝ} (membership : point ∈ cantorDust ratio) :
    ∃ digit : Bool, ∃ preimage ∈ cantorDust ratio, prefixExchangeMap ratio digit preimage = point := by
  have second_membership := membership.2
  rw [cantorSet_selfsimilar nonnegative less_one] at second_membership
  rcases second_membership with ⟨tail, tail_mem, representation⟩ | ⟨tail, tail_mem, representation⟩
  · refine ⟨false, (tail, point.1), ⟨tail_mem, membership.1⟩, ?_⟩
    apply Prod.ext
    · rfl
    · simpa [prefixExchangeMap, scalarWordMap] using representation
  · refine ⟨true, (tail, point.1), ⟨tail_mem, membership.1⟩, ?_⟩
    apply Prod.ext
    · rfl
    · simpa [prefixExchangeMap, scalarWordMap] using representation

theorem exchangedNormalizedFunction_contDiffAt {ratio slope : ℝ} (digit : Bool)
    (function : (ℝ × ℝ) → ℝ) {point : ℝ × ℝ}
    (smooth : ContDiffAt ℝ 2 function (prefixExchangeMap ratio digit point)) :
    ContDiffAt ℝ 2 (exchangedNormalizedFunction ratio slope digit function) point := by
  have composition := smooth.comp point (prefixExchangeMap_contDiff ratio digit).contDiffAt
  change ContDiffAt ℝ 2
    (fun value => function (prefixExchangeMap ratio digit value)/(ratio*slope)) point
  exact composition.div_const (ratio*slope)

theorem exchangedNormalizedFunction_hasStrictFDerivAt {ratio slope : ℝ}
    (ratio_positive : 0 < ratio) (slope_positive : 0 < slope) (digit : Bool)
    (function : (ℝ × ℝ) → ℝ) {point : ℝ × ℝ}
    (derivative : HasStrictFDerivAt function (positiveLinearContinuous slope)
      (prefixExchangeMap ratio digit point)) :
    HasStrictFDerivAt (exchangedNormalizedFunction ratio slope digit function)
      (positiveLinearContinuous (1/(ratio*slope))) point := by
  have map_derivative :=
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := point)).prodMk
      (((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := point)).const_mul ratio).const_add
        (if digit then 1-ratio else 0))
  change HasStrictFDerivAt (prefixExchangeMap ratio digit)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ratio • ContinuousLinearMap.fst ℝ ℝ ℝ)) point at map_derivative
  have normalized := (derivative.comp point map_derivative).const_mul (ratio*slope)⁻¹
  refine (normalized.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)).congr_fderiv ?_
  · intro value
    change (ratio*slope)⁻¹*function (prefixExchangeMap ratio digit value) =
      function (prefixExchangeMap ratio digit value)/(ratio*slope)
    rw [div_eq_mul_inv]
    exact mul_comm _ _
  · apply ContinuousLinearMap.ext
    intro value
    change (ratio*slope)⁻¹*(value.2+slope*(ratio*value.1)) =
      value.1+(1/(ratio*slope))*value.2
    field_simp [ratio_positive.ne', slope_positive.ne']
    <;> ring

theorem exchangedNormalizedFunction_isolated_pullback {ratio slope : ℝ}
    (ratio_positive : 0 < ratio) (ratio_less_one : ratio < 1) (slope_positive : 0 < slope)
    (digit : Bool) (function : (ℝ × ℝ) → ℝ)
    (point : {value | value ∈ cantorDust ratio ∧ function value = 0})
    (preimage : {value | value ∈ cantorDust ratio ∧
      exchangedNormalizedFunction ratio slope digit function value = 0})
    (representation : prefixExchangeMap ratio digit preimage.val = point.val)
    (isolated : IsOpen ({point} : Set {value | value ∈ cantorDust ratio ∧ function value = 0})) :
    IsOpen ({preimage} : Set {value | value ∈ cantorDust ratio ∧
      exchangedNormalizedFunction ratio slope digit function value = 0}) := by
  apply isolated_point_pullback (prefixExchangeMap ratio digit)
    (prefixExchangeMap_contDiff ratio digit).continuous (prefixExchangeMap_injective ratio_positive digit)
    _ point preimage representation isolated
  intro value membership
  refine ⟨prefixExchangeMap_mem_dust ratio_positive.le ratio_less_one digit membership.1, ?_⟩
  have zero := membership.2
  unfold exchangedNormalizedFunction at zero
  exact (div_eq_zero_iff.mp zero).resolve_right (mul_ne_zero ratio_positive.ne' slope_positive.ne')

theorem prefixExchangeMap_coordinates_mem_parameterField {ratio : ℝ} (digit : Bool)
    {point : ℝ × ℝ} (first_mem : point.1 ∈ parameterField ratio)
    (second_mem : point.2 ∈ parameterField ratio) :
    (prefixExchangeMap ratio digit point).1 ∈ parameterField ratio ∧
      (prefixExchangeMap ratio digit point).2 ∈ parameterField ratio :=
  ⟨second_mem, scalarWordMap_mem_parameterField [digit] first_mem⟩

theorem prefixExchangeMap_preimage_algebraic {ratio : ℝ} (ratio_positive : 0 < ratio)
    (ratio_algebraic : IsAlgebraic ℚ ratio) (digit : Bool) {point preimage : ℝ × ℝ}
    (representation : prefixExchangeMap ratio digit preimage = point)
    (first_algebraic : IsAlgebraic ℚ point.1) (second_algebraic : IsAlgebraic ℚ point.2) :
    IsAlgebraic ℚ preimage.1 ∧ IsAlgebraic ℚ preimage.2 := by
  have first_representation := congrArg Prod.fst representation
  have second_representation := congrArg Prod.snd representation
  constructor
  · apply scalarWordMap_tail_algebraic ratio_positive ratio_algebraic [digit]
    change IsAlgebraic ℚ (scalarWordMap ratio [digit] preimage.1)
    rw [show scalarWordMap ratio [digit] preimage.1 = point.2 from second_representation]
    exact second_algebraic
  · change preimage.2 = point.1 at first_representation
    rw [first_representation]
    exact first_algebraic

end LambdaCantor.Last
