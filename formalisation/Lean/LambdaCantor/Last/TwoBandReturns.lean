import LambdaCantor.Last.TwoBandAffine
import LambdaCantor.Last.LocalSource

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

theorem two_band_linear_central_entry {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope) (hlevel : level ∈ Set.Ioo (0 : ℝ) (1 + slope)) :
    ∃ word : List (Bool × Bool),
      linearWordReturn ratio (positiveLinear slope) word level ∈
        Set.Ioo (1 - ratio) (slope + ratio) := by
  have hless : ratio < 1 := by linarith
  have hlower : 0 < 1 - ratio := by linarith
  have hoverlap : 1 - ratio < ratio * (slope + ratio) := by
    have hbound := (bands.common_inequalities hpositive hhalf).1
    nlinarith
  by_cases hbelow : level < slope + ratio
  · obtain ⟨depth, hdepth⟩ := geometric_shell_entry hpositive hless hlower hoverlap hlevel.1 hbelow
    exact ⟨List.replicate depth (false, false), by rwa [linear_return_zero_word]⟩
  · have hreflected_pos : 0 < 1 + slope - level := by linarith [hlevel.2]
    have hreflected_upper : 1 + slope - level < slope + ratio := by linarith [bands.1]
    obtain ⟨depth, hdepth⟩ := geometric_shell_entry hpositive hless hlower hoverlap
      hreflected_pos hreflected_upper
    refine ⟨List.replicate depth (true, true), ?_⟩
    rw [linear_return_one_word ratio slope level hpositive.ne']
    constructor <;> linarith [hdepth.1, hdepth.2]

/-- Two strict returns on the same compact central domain as the established
return core, now for both full slope bands of Lemma 4.1. -/
theorem two_band_closed_central_strict_returns {ratio slope level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (bands : TwoBandSlopes ratio slope)
    (hlevel : level ∈ Set.Icc (1 - ratio) (slope + ratio)) :
    ∃ pair : ReturnPair,
      linearWordReturn ratio (positiveLinear slope) (pair.word false) level ∈
        interior (Set.Icc (1 - ratio) (slope + ratio)) ∧
      linearWordReturn ratio (positiveLinear slope) (pair.word true) level ∈
        interior (Set.Icc (1 - ratio) (slope + ratio)) := by
  have hwhole : level ∈ Set.Ioo (0 : ℝ) (1 + slope) :=
    ⟨by linarith [hlevel.1], by linarith [hlevel.2]⟩
  obtain ⟨common, firstDigit, secondDigit, hdifferent, hfirst, hsecond⟩ :=
    two_band_affine_strict_overlap hpositive hhalf bands hwhole
  obtain ⟨firstRest, hfirstRest⟩ := two_band_linear_central_entry hpositive hhalf bands
    ((affine_child_interior_iff hpositive _).mp hfirst)
  obtain ⟨secondRest, hsecondRest⟩ := two_band_linear_central_entry hpositive hhalf bands
    ((affine_child_interior_iff hpositive _).mp hsecond)
  let pair : ReturnPair := {
    word := fun bit => if bit then common ++ secondDigit :: secondRest else common ++ firstDigit :: firstRest
    length_pos := by intro bit; cases bit <;> simp
    diverge := ⟨common, firstDigit, secondDigit, firstRest, secondRest, hdifferent, rfl, rfl⟩ }
  refine ⟨pair, ?_, ?_⟩
  · change linearWordReturn ratio (positiveLinear slope) (common ++ ([firstDigit] ++ firstRest)) level ∈ _
    rw [linearWordReturn_append ratio hpositive.ne', linearWordReturn_append ratio hpositive.ne', interior_Icc]
    exact hfirstRest
  · change linearWordReturn ratio (positiveLinear slope) (common ++ ([secondDigit] ++ secondRest)) level ∈ _
    rw [linearWordReturn_append ratio hpositive.ne', linearWordReturn_append ratio hpositive.ne', interior_Icc]
    exact hsecondRest

/-- The actual nonlinear robust-source terminal, with both new bands. -/
theorem two_band_local_source_criterion (ratio slope : ℝ)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2) (bands : TwoBandSlopes ratio slope) :
    ∃ threshold : ℝ, 0 < threshold ∧ ∃ neighborhood : Set ℝ,
      IsOpen neighborhood ∧ Set.Icc (1 - ratio) (slope + ratio) ⊆ neighborhood ∧
      ∀ bound : ℝ≥0, (bound : ℝ) < threshold →
      ∀ function : (ℝ × ℝ) → ℝ, ∀ level : ℝ, ∀ word : List (Bool × Bool),
      LipschitzOnWith bound
        (fun value => function value - positiveLinearContinuous slope value) (wordCylinder ratio word) →
      (level - function (wordMap ratio word 0)) / ratio ^ word.length ∈ neighborhood →
      0 < dimH {point : ℝ × ℝ | point ∈ cantorDust ratio ∧ function point = level} := by
  apply local_source_criterion ratio hpositive hhalf (positiveLinearContinuous slope)
    (Set.Icc (1 - ratio) (slope + ratio)) isCompact_Icc
    (Set.nonempty_Icc.mpr (by linarith [bands.1]))
  exact fun level hlevel => two_band_closed_central_strict_returns hpositive hhalf bands hlevel

end LambdaCantor.Last
