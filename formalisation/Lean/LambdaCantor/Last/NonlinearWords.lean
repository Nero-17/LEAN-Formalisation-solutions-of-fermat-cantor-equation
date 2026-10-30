import LambdaCantor.Last.NonlinearGeometry
import LambdaCantor.Last.LinearReturns

noncomputable section
namespace LambdaCantor.Last

theorem CoordinateGrowth.word_restriction
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hpositive : 0 < ratio) (hless : ratio < 1) (word : List (Bool × Bool)) :
    CoordinateGrowth (function ∘ wordMap ratio word)
      (ratio ^ word.length * lowerS) (ratio ^ word.length * upperS)
      (ratio ^ word.length * lowerT) (ratio ^ word.length * upperT) := by
  have hzero := wordMap_mem_dust hpositive.le hless word
    (show (0 : ℝ × ℝ) ∈ cantorDust ratio from
      ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩)
  have hone := wordMap_mem_dust hpositive.le hless word
    (show ((1 : ℝ), (1 : ℝ)) ∈ cantorDust ratio from
      ⟨one_mem_cantorSet hpositive.le hless, one_mem_cantorSet hpositive.le hless⟩)
  have hzeroS := cantorSet_subset_unitInterval hpositive.le hless hzero.1
  have hzeroT := cantorSet_subset_unitInterval hpositive.le hless hzero.2
  have honeS := cantorSet_subset_unitInterval hpositive.le hless hone.1
  have honeT := cantorSet_subset_unitInterval hpositive.le hless hone.2
  rw [wordMap_affine] at honeS honeT
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one] at honeS honeT
  have hrestricted := growth.restrict_square hzeroS.1 hzeroT.1
    (pow_pos hpositive word.length).le honeS.2 honeT.2
  convert hrestricted using 1
  funext point
  rw [Function.comp_apply, wordMap_affine]
  rfl

/-- The central-entry statement expressed in actual finite Cantor words. -/
theorem nonlinear_central_word
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : Continuous function)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hoverlap : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1))) :
    ∃ word : List (Bool × Bool), level ∈ Set.Ioo
      (function (wordMap ratio word (1 - ratio, 0)))
      (function (wordMap ratio word (ratio, 1))) := by
  rcases nonlinear_central_entry growth hcontinuous.continuousAt hcontinuous.continuousAt
    hpositive hhalf hlowerS hslope hoverlap hlevel with ⟨depth, hdepth⟩ | ⟨depth, hdepth⟩
  · refine ⟨List.replicate depth (false, false), ?_⟩
    have hfirst : wordMap ratio (List.replicate depth (false, false)) (1 - ratio, 0) =
        ((1 - ratio) * ratio ^ depth, 0) := by
      rw [wordMap_affine, wordMap_replicate_zero]
      ext <;> simp [mul_comm]
    have hsecond : wordMap ratio (List.replicate depth (false, false)) (ratio, 1) =
        (ratio * ratio ^ depth, ratio ^ depth) := by
      rw [wordMap_affine, wordMap_replicate_zero]
      ext <;> simp [mul_comm]
    rwa [hfirst, hsecond]
  · refine ⟨List.replicate depth (true, true), ?_⟩
    have hfirst : wordMap ratio (List.replicate depth (true, true)) (1 - ratio, 0) =
        (1 - ratio * ratio ^ depth, 1 - ratio ^ depth) := by
      rw [wordMap_affine, wordMap_replicate_one]
      ext <;> simp only [List.length_replicate, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_zero, add_zero] <;> ring
    have hsecond : wordMap ratio (List.replicate depth (true, true)) (ratio, 1) =
        (1 - (1 - ratio) * ratio ^ depth, 1) := by
      rw [wordMap_affine, wordMap_replicate_one]
      ext <;> simp only [List.length_replicate, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one] <;> ring
    rwa [hfirst, hsecond]

theorem nonlinear_central_children
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hoverlap : (1 - 2 * ratio) * upperT < ratio * lowerS)
    (hlevel : level ∈ Set.Ioo (function (1 - ratio, 0)) (function (ratio, 1))) :
    ∃ first second : Bool × Bool, first ≠ second ∧
      level ∈ Set.Ioo (function (wordMap ratio [first] 0))
        (function (wordMap ratio [first] (1, 1))) ∧
      level ∈ Set.Ioo (function (wordMap ratio [second] 0))
        (function (wordMap ratio [second] (1, 1))) := by
  have hlower : ∀ digit : Bool × Bool, wordMap ratio [digit] 0 =
      (if digit.1 then 1 - ratio else 0, if digit.2 then 1 - ratio else 0) := by
    rintro ⟨first, second⟩
    cases first <;> cases second <;> ext <;> simp [wordMap, digitPoint]
  have hupper : ∀ digit : Bool × Bool, wordMap ratio [digit] (1, 1) =
      (if digit.1 then 1 else ratio, if digit.2 then 1 else ratio) := by
    rintro ⟨first, second⟩
    cases first <;> cases second <;> ext <;> simp [wordMap, digitPoint] <;> ring
  rcases nonlinear_central_double_cover growth hpositive hhalf hlowerS hslope hoverlap hlevel
    with hpair | hpair | hpair
  · refine ⟨(false, false), (true, false), by decide, ?_⟩
    simpa [hlower, hupper] using hpair
  · refine ⟨(true, false), (false, true), by decide, ?_⟩
    simpa [hlower, hupper] using hpair
  · refine ⟨(false, true), (true, true), by decide, ?_⟩
    simpa [hlower, hupper] using hpair

/-- Every interior fibre admits two incomparable finite descendants whose corner
values still strictly bracket the level. -/
theorem nonlinear_two_descendants
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : Continuous function)
    (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hshell : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hoverlap : (1 - 2 * ratio) * upperT < ratio * lowerS)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1))) :
    ∃ first second : List (Bool × Bool),
      0 < first.length ∧ 0 < second.length ∧ WordsDiverge first second ∧
      level ∈ Set.Ioo (function (wordMap ratio first 0))
        (function (wordMap ratio first (1, 1))) ∧
      level ∈ Set.Ioo (function (wordMap ratio second 0))
        (function (wordMap ratio second (1, 1))) := by
  obtain ⟨common, hcommon⟩ := nonlinear_central_word growth hcontinuous hpositive hhalf
    hlowerS hslope hshell hlevel
  have hscale : 0 < ratio ^ common.length := pow_pos hpositive _
  obtain ⟨first, second, hdifferent, hfirst, hsecond⟩ := nonlinear_central_children
    (growth.word_restriction hpositive (by linarith) common) hpositive hhalf
    (mul_pos hscale hlowerS) (mul_lt_mul_of_pos_left hslope hscale)
    (by nlinarith [mul_lt_mul_of_pos_left hoverlap hscale]) hcommon
  refine ⟨common ++ [first], common ++ [second], by simp, by simp,
    ⟨common, first, second, [], [], hdifferent, rfl, rfl⟩, ?_, ?_⟩
  · simpa only [wordMap_append, Function.comp_apply] using hfirst
  · simpa only [wordMap_append, Function.comp_apply] using hsecond

end LambdaCantor.Last
