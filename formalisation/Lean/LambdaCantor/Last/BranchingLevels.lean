import LambdaCantor.Last.LinearReturns

noncomputable section
namespace LambdaCantor.Last

theorem nonzero_child_linear_lower {ratio slope : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (hslope : 1 < slope)
    (digit : Bool × Bool) (hnonzero : digit ≠ (false, false))
    {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    1 - ratio ≤ positiveLinear slope (wordMap ratio [digit] point) := by
  obtain ⟨hx0, hx1⟩ := cantorSet_subset_unitInterval hratio hless hpoint.1
  obtain ⟨hy0, hy1⟩ := cantorSet_subset_unitInterval hratio hless hpoint.2
  rcases digit with ⟨firstDigit, secondDigit⟩
  cases firstDigit <;> cases secondDigit
  · exact False.elim (hnonzero rfl)
  all_goals
    simp only [wordMap, digitPoint, if_true, Bool.false_eq_true, if_false,
      positiveLinear, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zero, mul_one, zero_add]
    nlinarith [mul_nonneg hratio hx0, mul_nonneg hratio hy0,
      mul_nonneg (show 0 ≤ slope by linarith) (mul_nonneg hratio hy0)]

theorem nontop_child_linear_upper {ratio slope : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (hslope : 1 < slope)
    (digit : Bool × Bool) (hnontop : digit ≠ (true, true))
    {point : ℝ × ℝ} (hpoint : point ∈ cantorDust ratio) :
    positiveLinear slope (wordMap ratio [digit] point) ≤ slope + ratio := by
  obtain ⟨hx0, hx1⟩ := cantorSet_subset_unitInterval hratio hless hpoint.1
  obtain ⟨hy0, hy1⟩ := cantorSet_subset_unitInterval hratio hless hpoint.2
  have hxbound : ratio * point.1 ≤ ratio := mul_le_of_le_one_right hratio hx1
  have hybound : ratio * point.2 ≤ ratio := mul_le_of_le_one_right hratio hy1
  have hsbound : slope * (ratio * point.2) ≤ slope * ratio :=
    mul_le_mul_of_nonneg_left hybound (by linarith)
  rcases digit with ⟨firstDigit, secondDigit⟩
  cases firstDigit <;> cases secondDigit
  all_goals
    first
    | exact False.elim (hnontop rfl)
    | simp only [wordMap, digitPoint, if_true, Bool.false_eq_true, if_false,
        positiveLinear, LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zero, mul_one, zero_add]
      nlinarith

/-- Two distinct child points of one perturbed level force its normalized level
to lie within the error bound of the closed central interval. -/
theorem branching_level_bounds {ratio slope level bound : ℝ}
    (hratio : 0 ≤ ratio) (hless : ratio < 1) (hslope : 1 < slope)
    (error : (ℝ × ℝ) → ℝ)
    (herror : ∀ point ∈ cantorDust ratio, |error point| ≤ bound)
    (firstDigit secondDigit : Bool × Bool) (hdifferent : firstDigit ≠ secondDigit)
    (first second : ℝ × ℝ) (hfirst : first ∈ cantorDust ratio) (hsecond : second ∈ cantorDust ratio)
    (hfirst_level : positiveLinear slope (wordMap ratio [firstDigit] first) +
      error (wordMap ratio [firstDigit] first) = level)
    (hsecond_level : positiveLinear slope (wordMap ratio [secondDigit] second) +
      error (wordMap ratio [secondDigit] second) = level) :
    1 - ratio - bound ≤ level ∧ level ≤ slope + ratio + bound := by
  have hfirst_error := abs_le.mp (herror _ (wordMap_mem_dust hratio hless [firstDigit] hfirst))
  have hsecond_error := abs_le.mp (herror _ (wordMap_mem_dust hratio hless [secondDigit] hsecond))
  constructor
  · by_cases hzero : firstDigit = (false, false)
    · have hsecond_nonzero : secondDigit ≠ (false, false) := by
        intro heq
        exact hdifferent (hzero.trans heq.symm)
      have := nonzero_child_linear_lower hratio hless hslope secondDigit hsecond_nonzero hsecond
      linarith
    · have := nonzero_child_linear_lower hratio hless hslope firstDigit hzero hfirst
      linarith
  · by_cases htop : firstDigit = (true, true)
    · have hsecond_nontop : secondDigit ≠ (true, true) := by
        intro heq
        exact hdifferent (htop.trans heq.symm)
      have := nontop_child_linear_upper hratio hless hslope secondDigit hsecond_nontop hsecond
      linarith
    · have := nontop_child_linear_upper hratio hless hslope firstDigit htop hfirst
      linarith

theorem open_interval_neighborhood_margin {lower upper : ℝ} (horder : lower ≤ upper)
    {neighborhood : Set ℝ} (hopen : IsOpen neighborhood)
    (hcontains : Set.Icc lower upper ⊆ neighborhood) :
    ∃ margin : ℝ, 0 < margin ∧ ∀ value : ℝ,
      lower - margin < value → value < upper + margin → value ∈ neighborhood := by
  obtain ⟨lowerRadius, hlowerRadius, hlowerBall⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (hcontains ⟨le_rfl, horder⟩))
  obtain ⟨upperRadius, hupperRadius, hupperBall⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (hcontains ⟨horder, le_rfl⟩))
  refine ⟨min lowerRadius upperRadius, lt_min hlowerRadius hupperRadius, ?_⟩
  intro value hlower hupper
  by_cases hbelow : value < lower
  · apply hlowerBall
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hbelow)]
    linarith [min_le_left lowerRadius upperRadius]
  · by_cases habove : upper < value
    · apply hupperBall
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr habove)]
      linarith [min_le_right lowerRadius upperRadius]
    · exact hcontains ⟨le_of_not_gt hbelow, le_of_not_gt habove⟩

end LambdaCantor.Last
