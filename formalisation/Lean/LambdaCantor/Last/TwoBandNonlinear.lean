import LambdaCantor.Last.TwoBandReturns
import LambdaCantor.Last.NonlinearFibres

noncomputable section
namespace LambdaCantor.Last

theorem four_interval_strict_cover {lower0 lower1 lower2 lower3 upper0 upper1 upper2 upper3 level : ℝ}
    (hoverlap01 : lower1 < upper0) (hoverlap12 : lower2 < upper1)
    (hoverlap23 : lower3 < upper2) (hlevel : level ∈ Set.Ioo lower0 upper3) :
    level ∈ Set.Ioo lower0 upper0 ∨ level ∈ Set.Ioo lower1 upper1 ∨
      level ∈ Set.Ioo lower2 upper2 ∨ level ∈ Set.Ioo lower3 upper3 := by
  by_cases hfirst : level < upper0
  · exact Or.inl ⟨hlevel.1, hfirst⟩
  · by_cases hsecond : level < upper1
    · exact Or.inr (Or.inl ⟨by linarith, hsecond⟩)
    · by_cases hthird : level < upper2
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, hthird⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, hlevel.2⟩))

/-- Strict consecutive overlaps suffice for one continuing strict child.
These inequalities are weaker than the old double-cover hypothesis. -/
theorem nonlinear_one_strict_child
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (houter : (1 - 2 * ratio) * upperS < ratio * lowerT)
    (hmiddle : (1 - 2 * ratio) * upperT < lowerS)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1))) :
    ∃ digit : Bool × Bool, level ∈ Set.Ioo (function (wordMap ratio [digit] 0))
      (function (wordMap ratio [digit] (1, 1))) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hr : ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨hpositive.le, by linarith⟩
  have hc : 1 - ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hoverlap01 : function (1 - ratio, 0) < function (ratio, ratio) := by
    have hbound := growth.mixed_upper hr hc hzero hr (by linarith) hpositive.le
    nlinarith [hbound]
  have hoverlap12 : function (0, 1 - ratio) < function (1, ratio) := by
    have hbound := growth.mixed_lower hzero hone hr hc zero_le_one (by linarith)
    nlinarith [hbound]
  have hoverlap23 : function (1 - ratio, 1 - ratio) < function (ratio, 1) := by
    have hbound := growth.mixed_upper hr hc hc hone (by linarith) (by linarith)
    nlinarith [hbound]
  rcases four_interval_strict_cover hoverlap01 hoverlap12 hoverlap23 hlevel with first | second | third | fourth
  · exact ⟨(false, false), by simpa [wordMap, digitPoint] using first⟩
  · exact ⟨(true, false), by simpa [wordMap, digitPoint] using second⟩
  · exact ⟨(false, true), by simpa [wordMap, digitPoint] using third⟩
  · exact ⟨(true, true), by simpa [wordMap, digitPoint] using fourth⟩

/-- A single strict child at each stage gives arbitrarily deep genuine interior
cylinders through one point of the fibre. No branching assumption is used. -/
theorem deep_interior_cylinders_of_child_cover
    {function : (ℝ × ℝ) → ℝ} {ratio level : ℝ}
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2) (hcontinuous : Continuous function)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1)))
    (hcover : ∀ parent : InteriorCylinder ratio function level,
      ∃ digit : Bool × Bool, level ∈ Set.Ioo
        (function (wordMap ratio (parent.word ++ [digit]) 0))
        (function (wordMap ratio (parent.word ++ [digit]) (1, 1)))) :
    ∃ point ∈ cantorDust ratio, function point = level ∧
      ∀ minimumDepth : ℕ, ∃ word : List (Bool × Bool), minimumDepth ≤ word.length ∧
        point ∈ wordCylinder ratio word ∧ level ∈ Set.Ioo
          (function (wordMap ratio word 0)) (function (wordMap ratio word (1, 1))) := by
  classical
  let selected : InteriorCylinder ratio function level → Bool × Bool := fun parent => (hcover parent).choose
  let system : VariableWordSystem (InteriorCylinder ratio function level) := {
    word := fun parent _ => [selected parent]
    next := fun parent _ => ⟨parent.word ++ [selected parent], (hcover parent).choose_spec⟩
    length_pos := by intros; simp }
  let initial : InteriorCylinder ratio function level := ⟨[], by
    change level ∈ Set.Ioo (function (0, 0)) (function (1, 1))
    exact hlevel⟩
  have hless : ratio < 1 := by linarith
  have hwords : ∀ branch depth, (system.run initial branch depth).1.word =
      (system.run initial branch depth).2 := by
    intro branch depth
    induction depth with
    | zero => rfl
    | succ depth ih => simp only [VariableWordSystem.run, system]; rw [ih]
  let point := (system.compactTree ratio hpositive hless initial).coding (fun _ => false)
  refine ⟨point, system.coding_mem_dust ratio hpositive hless initial _, ?_, ?_⟩
  · apply system.coding_level ratio hpositive hless initial function level hcontinuous.continuousOn
    intro branch depth
    have hbrackets := (system.run initial branch depth).1.interior_level
    rw [hwords] at hbrackets
    exact ⟨hbrackets.1.le, hbrackets.2.le⟩
  · intro minimumDepth
    refine ⟨(system.run initial (fun _ => false) minimumDepth).2,
      system.run_length initial _ _, (system.compactTree ratio hpositive hless initial).coding_mem _ _, ?_⟩
    have hbrackets := (system.run initial (fun _ => false) minimumDepth).1.interior_level
    rwa [hwords] at hbrackets

/-- Every level in the closed hull is realized on the actual Cantor dust.
This uses only consecutive child overlaps, not the two-band return theorem. -/
theorem nonlinear_closed_hull_filled
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : Continuous function) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (houter : (1 - 2 * ratio) * upperS < ratio * lowerT)
    (hmiddle : (1 - 2 * ratio) * upperT < lowerS)
    (hlevel : level ∈ Set.Icc (function (0, 0)) (function (1, 1))) :
    ∃ point ∈ cantorDust ratio, function point = level := by
  have hless : ratio < 1 := by linarith
  rcases eq_or_lt_of_le hlevel.1 with hzero | hlower
  · exact ⟨0, ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩, hzero⟩
  rcases lt_or_eq_of_le hlevel.2 with hupper | hone
  · have hcover : ∀ parent : InteriorCylinder ratio function level,
        ∃ digit : Bool × Bool, level ∈ Set.Ioo
          (function (wordMap ratio (parent.word ++ [digit]) 0))
          (function (wordMap ratio (parent.word ++ [digit]) (1, 1))) := by
      intro parent
      have hscale : 0 < ratio ^ parent.word.length := pow_pos hpositive _
      obtain ⟨digit, hdigit⟩ := nonlinear_one_strict_child
        (growth.word_restriction hpositive hless parent.word) hpositive hhalf
        (by nlinarith [mul_lt_mul_of_pos_left houter hscale])
        (by nlinarith [mul_lt_mul_of_pos_left hmiddle hscale]) parent.interior_level
      exact ⟨digit, by simpa only [wordMap_append, Function.comp_apply] using hdigit⟩
    obtain ⟨point, hpoint, hpoint_level, hdeep⟩ := deep_interior_cylinders_of_child_cover
      hpositive hhalf hcontinuous ⟨hlower, hupper⟩ hcover
    exact ⟨point, hpoint, hpoint_level⟩
  · exact ⟨(1, 1), ⟨one_mem_cantorSet hpositive.le hless, one_mem_cantorSet hpositive.le hless⟩, hone.symm⟩

theorem nonlinear_word_closed_hull_filled
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : Continuous function) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (houter : (1 - 2 * ratio) * upperS < ratio * lowerT)
    (hmiddle : (1 - 2 * ratio) * upperT < lowerS) (word : List (Bool × Bool))
    (hlevel : level ∈ Set.Icc (function (wordMap ratio word 0))
      (function (wordMap ratio word (1, 1)))) :
    ∃ point ∈ wordCylinder ratio word, function point = level := by
  have hless : ratio < 1 := by linarith
  have hscale : 0 < ratio ^ word.length := pow_pos hpositive _
  obtain ⟨tail, htail, htail_level⟩ := nonlinear_closed_hull_filled
    (growth.word_restriction hpositive hless word) (hcontinuous.comp (continuous_wordMap ratio word))
    hpositive hhalf (by nlinarith [mul_lt_mul_of_pos_left houter hscale])
    (by nlinarith [mul_lt_mul_of_pos_left hmiddle hscale]) hlevel
  exact ⟨wordMap ratio word tail, ⟨tail, htail, rfl⟩, htail_level⟩

end LambdaCantor.Last
