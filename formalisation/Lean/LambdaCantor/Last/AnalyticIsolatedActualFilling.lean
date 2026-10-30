import LambdaCantor.Last.AnalyticIsolatedFilling

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

def normalizedActualFunction (function : (ℝ × ℝ) → ℝ) (ratio : ℝ)
    (word : List (Bool × Bool)) (point : ℝ × ℝ) : ℝ :=
  (function (wordMap ratio word point)-function (wordMap ratio word 0))/ratio^word.length

/-- Small actual linearization error on the dust is enough to fill each
actual closed child hull. The Lipschitz extension is used only to apply the
covering argument, and agreement is retained at every resulting dust point. -/
theorem actual_child_hull_filled_of_cylinder_error {ratio slope : ℝ}
    (positive : 0 < ratio) (less_half : ratio < 1/2)
    (function : (ℝ × ℝ) → ℝ) (word : List (Bool × Bool)) {bound : ℝ≥0}
    (error_lipschitz : LipschitzOnWith bound
      (fun value => function value-positiveLinearContinuous slope value) (wordCylinder ratio word))
    (outer : (1-2*ratio)*(1+(bound : ℝ)) < ratio*(slope-bound))
    (middle : (1-2*ratio)*(slope+(bound : ℝ)) < 1-bound)
    (digit : Bool × Bool) {level : ℝ}
    (brackets : level ∈ Set.Icc
      (function (wordMap ratio word (wordMap ratio [digit] 0)))
      (function (wordMap ratio word (wordMap ratio [digit] (1,1))))) :
    ∃ tail ∈ cantorDust ratio,
      function (wordMap ratio word (wordMap ratio [digit] tail)) = level := by
  have less_one : ratio < 1 := by linarith
  have scale_positive : 0 < ratio^word.length := pow_pos positive _
  obtain ⟨extension, extension_lipschitz, agreement⟩ := error_lipschitz.extend_real
  have normalized_lipschitz := normalizedError_lipschitz extension_lipschitz
    (ratio^word.length) scale_positive (wordMap ratio word 0)
  have actual_agreement : ∀ point ∈ cantorDust ratio,
      normalizedActualFunction function ratio word point = point.1+slope*point.2+
        normalizedError extension (ratio^word.length) (wordMap ratio word 0) point := by
    intro point point_in_dust
    symm
    exact normalized_fibre_equation positive (positiveLinearContinuous slope) function extension
      word agreement (function (wordMap ratio word point)) point_in_dust rfl
  have first_in_dust : wordMap ratio [digit] 0 ∈ cantorDust ratio :=
    wordMap_mem_dust positive.le less_one _ ⟨zero_mem_cantorSet ratio, zero_mem_cantorSet ratio⟩
  have last_in_dust : wordMap ratio [digit] (1,1) ∈ cantorDust ratio :=
    wordMap_mem_dust positive.le less_one _
      ⟨one_mem_cantorSet positive.le less_one, one_mem_cantorSet positive.le less_one⟩
  have normalized_brackets : (level-function (wordMap ratio word 0))/ratio^word.length ∈ Set.Icc
      ((fun point => point.1+slope*point.2+
        normalizedError extension (ratio^word.length) (wordMap ratio word 0) point)
          (wordMap ratio [digit] 0))
      ((fun point => point.1+slope*point.2+
        normalizedError extension (ratio^word.length) (wordMap ratio word 0) point)
          (wordMap ratio [digit] (1,1))) := by
    dsimp only
    rw [← actual_agreement _ first_in_dust, ← actual_agreement _ last_in_dust]
    unfold normalizedActualFunction
    constructor
    · exact (div_le_div_iff_of_pos_right scale_positive).mpr (sub_le_sub_right brackets.1 _)
    · exact (div_le_div_iff_of_pos_right scale_positive).mpr (sub_le_sub_right brackets.2 _)
  obtain ⟨point, point_in_child, point_level⟩ := lipschitz_perturbed_word_hull_filled
    positive less_half normalized_lipschitz outer middle [digit] normalized_brackets
  have point_in_dust := wordCylinder_subset_dust positive.le less_one [digit] point_in_child
  have normalized_level := (actual_agreement point point_in_dust).trans point_level
  change (function (wordMap ratio word point)-function (wordMap ratio word 0))/ratio^word.length =
    (level-function (wordMap ratio word 0))/ratio^word.length at normalized_level
  have cleared := congrArg (fun value : ℝ => value*ratio^word.length) normalized_level
  simp only [div_mul_cancel₀ _ scale_positive.ne'] at cleared
  have actual_level : function (wordMap ratio word point) = level := by linarith
  obtain ⟨tail, tail_in_dust, representation⟩ := point_in_child
  exact ⟨tail, tail_in_dust, by simpa [representation] using actual_level⟩

end LambdaCantor.Last
