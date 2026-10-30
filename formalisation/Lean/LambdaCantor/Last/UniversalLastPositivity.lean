import LambdaCantor.Last.UniversalLastConclusion

noncomputable section
namespace LambdaCantor.Last

theorem positive_dimension_above_lastTransition {exponent ratio : ℝ}
    (hratio : ratio ∈ Set.Ioc (0 : ℝ) (1 / 2))
    (habove : lastTransition exponent < ratio) :
    0 < dimH (intersection exponent ratio) := by
  by_contra hfailure
  have hzero : dimH (intersection exponent ratio) = 0 :=
    le_antisymm (le_of_not_gt hfailure) bot_le
  exact (not_lt_of_ge (le_lastTransition_of_zero hratio hzero)) habove

theorem universal_positive_dimension_at_or_above_critical {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hcritical : (Real.sqrt 3 - 1) / 2 ≤ ratio)
    (hhalf : ratio ≤ 1 / 2) : 0 < dimH (intersection exponent ratio) := by
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonnegative := Real.sqrt_nonneg (3 : ℝ)
  have hratio : 0 < ratio := by nlinarith
  exact positive_dimension_above_lastTransition ⟨hratio, hhalf⟩
    ((universal_lastTransition_lt_critical hexponent).trans_le hcritical)

theorem universal_positive_dimension_near_critical {exponent : ℝ}
    (hexponent : 1 < exponent) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ ratio ∈ Set.Ioc (0 : ℝ) (1 / 2),
        (Real.sqrt 3 - 1) / 2 - radius < ratio →
        0 < dimH (intersection exponent ratio) := by
  have hlast := universal_lastTransition_lt_critical hexponent
  refine ⟨(((Real.sqrt 3 - 1) / 2) - lastTransition exponent) / 2, by linarith, ?_⟩
  intro ratio hratio habove
  exact positive_dimension_above_lastTransition hratio (by linarith)

end LambdaCantor.Last

#print axioms LambdaCantor.Last.positive_dimension_above_lastTransition
#print axioms LambdaCantor.Last.universal_positive_dimension_at_or_above_critical
#print axioms LambdaCantor.Last.universal_positive_dimension_near_critical
