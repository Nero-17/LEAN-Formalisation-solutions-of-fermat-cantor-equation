import LambdaCantor.Last.PositiveDerivatives
import LambdaCantor.Last.ReturnAtlas

noncomputable section
namespace LambdaCantor.Last

theorem wordMap_replicate_zero (ratio : ℝ) (depth : ℕ) :
    wordMap ratio (List.replicate depth (false, false)) 0 = 0 := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [List.replicate_succ, wordMap, digitPoint, ih]

theorem wordMap_replicate_one (ratio : ℝ) (depth : ℕ) :
    wordMap ratio (List.replicate depth (true, true)) 0 =
      (1 - ratio ^ depth, 1 - ratio ^ depth) := by
  induction depth with
  | zero => ext <;> simp [wordMap]
  | succ depth ih =>
    simp only [List.replicate_succ, wordMap, ih, digitPoint, if_true, pow_succ]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem linear_return_zero_word (ratio slope level : ℝ) (depth : ℕ) :
    linearWordReturn ratio (positiveLinear slope) (List.replicate depth (false, false)) level =
      level / ratio ^ depth := by
  simp [linearWordReturn, returnLevel, wordMap_replicate_zero]

theorem linear_return_one_word (ratio slope level : ℝ) (hratio : ratio ≠ 0) (depth : ℕ) :
    linearWordReturn ratio (positiveLinear slope) (List.replicate depth (true, true)) level =
      1 + slope - (1 + slope - level) / ratio ^ depth := by
  simp only [linearWordReturn, returnLevel, List.length_replicate, wordMap_replicate_one,
    positiveLinear, LinearMap.coe_mk, AddHom.coe_mk]
  field_simp
  <;> ring

/-- Every strict level enters the central branching interval after a finite
word consisting entirely of bottom-left or top-right digits. -/
theorem linear_central_entry {ratio slope level : ℝ}
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hslopes : StrictSlopeConditions ratio slope)
    (hlevel : level ∈ Set.Ioo (0 : ℝ) (1 + slope)) :
    ∃ word : List (Bool × Bool),
      linearWordReturn ratio (positiveLinear slope) word level ∈
        Set.Ioo (1 - ratio) (slope + ratio) := by
  have hratio_one : ratio < 1 := by linarith
  have hlower : 0 < 1 - ratio := by linarith
  have hoverlap : 1 - ratio < ratio * (slope + ratio) := by
    have := hslopes.2.1
    nlinarith
  by_cases hbelow : level < slope + ratio
  · obtain ⟨depth, hdepth⟩ := geometric_shell_entry hratio hratio_one hlower hoverlap hlevel.1 hbelow
    exact ⟨List.replicate depth (false, false), by rwa [linear_return_zero_word]⟩
  · have hreflected_pos : 0 < 1 + slope - level := by linarith [hlevel.2]
    have hreflected_upper : 1 + slope - level < slope + ratio := by
      have := hslopes.1
      linarith
    obtain ⟨depth, hdepth⟩ := geometric_shell_entry hratio hratio_one hlower hoverlap
      hreflected_pos hreflected_upper
    refine ⟨List.replicate depth (true, true), ?_⟩
    rw [linear_return_one_word ratio slope level hratio.ne']
    constructor <;> linarith [hdepth.1, hdepth.2]

theorem normalized_interval {ratio level offset upper : ℝ} (hratio : 0 < ratio)
    (hlower : offset < level) (hupper : level < offset + ratio * upper) :
    (level - offset) / ratio ∈ Set.Ioo (0 : ℝ) upper := by
  constructor
  · exact div_pos (sub_pos.mpr hlower) hratio
  · rw [div_lt_iff₀ hratio]
    nlinarith

/-- Every level in the central interval lies strictly inside two different
first-generation image intervals. -/
theorem linear_central_two_children {ratio slope level : ℝ}
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hslopes : StrictSlopeConditions ratio slope)
    (hlevel : level ∈ Set.Ioo (1 - ratio) (slope + ratio)) :
    ∃ firstDigit secondDigit : Bool × Bool, firstDigit ≠ secondDigit ∧
      linearWordReturn ratio (positiveLinear slope) [firstDigit] level ∈ Set.Ioo 0 (1 + slope) ∧
      linearWordReturn ratio (positiveLinear slope) [secondDigit] level ∈ Set.Ioo 0 (1 + slope) := by
  have hslope : 1 < slope := hslopes.1
  have hgap : (1 - 2 * ratio) * slope < ratio := hslopes.2.2
  have hlevel_pos : 0 < level := by linarith [hlevel.1]
  by_cases hfirst_region : level ≤ (1 - ratio) * slope
  · refine ⟨(false, false), (true, false), by decide, ?_, ?_⟩
    · simpa [linearWordReturn, returnLevel, wordMap, digitPoint, positiveLinear] using
        normalized_interval hratio (offset := 0) (upper := 1 + slope) hlevel_pos (by nlinarith)
    · simpa [linearWordReturn, returnLevel, wordMap, digitPoint, positiveLinear] using
        normalized_interval hratio (offset := 1 - ratio) (upper := 1 + slope) hlevel.1 (by nlinarith)
  · by_cases hmiddle_region : level < 1 + ratio * slope
    · refine ⟨(true, false), (false, true), by decide, ?_, ?_⟩
      · simpa [linearWordReturn, returnLevel, wordMap, digitPoint, positiveLinear] using
          normalized_interval hratio (offset := 1 - ratio) (upper := 1 + slope) hlevel.1 (by nlinarith)
      · simpa [linearWordReturn, returnLevel, wordMap, digitPoint, positiveLinear, mul_comm] using
          normalized_interval hratio (offset := (1 - ratio) * slope) (upper := 1 + slope)
            (lt_of_not_ge hfirst_region) (by nlinarith [hlevel.2])
    · refine ⟨(false, true), (true, true), by decide, ?_, ?_⟩
      · simpa [linearWordReturn, returnLevel, wordMap, digitPoint, positiveLinear, mul_comm] using
          normalized_interval hratio (offset := (1 - ratio) * slope) (upper := 1 + slope)
            (lt_of_not_ge hfirst_region) (by nlinarith [hlevel.2])
      · simpa [linearWordReturn, returnLevel, wordMap, digitPoint, positiveLinear,
          mul_add, add_mul, mul_comm] using
          normalized_interval hratio (offset := (1 - ratio) * (1 + slope)) (upper := 1 + slope)
            (by nlinarith) (by nlinarith [hlevel.2])

/-- Two incomparable strict returns at every point of the closed central interval.
This avoids any cardinality argument by using explicit finite entry words. -/
theorem linear_closed_central_strict_returns {ratio slope level : ℝ}
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hslopes : StrictSlopeConditions ratio slope)
    (hlevel : level ∈ Set.Icc (1 - ratio) (slope + ratio)) :
    ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) level ∈
        interior (Set.Icc (1 - ratio) (slope + ratio)) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) level ∈
        interior (Set.Icc (1 - ratio) (slope + ratio)) := by
  have hwhole : level ∈ Set.Ioo (0 : ℝ) (1 + slope) :=
    ⟨by linarith [hlevel.1], by linarith [hlevel.2]⟩
  obtain ⟨common, hcommon⟩ := linear_central_entry hratio hhalf hslopes hwhole
  obtain ⟨firstDigit, secondDigit, hdifferent, hfirst, hsecond⟩ :=
    linear_central_two_children hratio hhalf hslopes hcommon
  obtain ⟨firstRest, hfirstRest⟩ := linear_central_entry hratio hhalf hslopes hfirst
  obtain ⟨secondRest, hsecondRest⟩ := linear_central_entry hratio hhalf hslopes hsecond
  let pair : ReturnPair := {
    word := fun bit => if bit then common ++ secondDigit :: secondRest else common ++ firstDigit :: firstRest
    length_pos := by intro bit; cases bit <;> simp
    diverge := ⟨common, firstDigit, secondDigit, firstRest, secondRest, hdifferent, rfl, rfl⟩ }
  refine ⟨pair, ?_, ?_⟩
  · change linearWordReturn ratio (positiveLinear slope) (common ++ ([firstDigit] ++ firstRest)) level ∈ _
    rw [linearWordReturn_append ratio hratio.ne', linearWordReturn_append ratio hratio.ne', interior_Icc]
    exact hfirstRest
  · change linearWordReturn ratio (positiveLinear slope) (common ++ ([secondDigit] ++ secondRest)) level ∈ _
    rw [linearWordReturn_append ratio hratio.ne', linearWordReturn_append ratio hratio.ne', interior_Icc]
    exact hsecondRest

end LambdaCantor.Last
