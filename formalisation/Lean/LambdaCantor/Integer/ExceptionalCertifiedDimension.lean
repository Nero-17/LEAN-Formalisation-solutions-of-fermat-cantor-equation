import LambdaCantor.Integer.ExceptionalSourceDimension
import LambdaCantor.Integer.ExceptionalIntervals

noncomputable section
namespace LambdaCantor.Integer.Exceptional

/-- The complete application of an exact finite return certificate to its actual
Fermat source. Every hypothesis is a finite source/interval/certificate fact;
the nonlinear realization and dimension transfer are proved internally. -/
theorem certified_source_positive_dimension (source : Source) (valid : source.Valid)
    (denominator : ℤ) (positive : 0 < denominator) (offsets : Fin 4 → ℤ)
    (outerIntervals innerIntervals : List (ℤ × ℤ)) (maximumDepth : ℕ)
    (depth_matches : source.returnDepth = maximumDepth)
    (offsets_exact : ∀ digit : Fin 4, (offsets digit : ℚ)/denominator =
      match digit.val with | 0 => 0 | 1 => 1 | 2 => source.slope | _ => source.slope+1)
    (outer_exact : outerIntervals.map (fun interval =>
      ((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator)) =
      [(1/3,(source.slope+1)/6),(source.slope/3,(source.slope+3)/6),
       ((source.slope+1)/3,(3*source.slope+1)/6)])
    (inner_exact : innerIntervals.map (fun interval =>
      ((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator)) =
      [(1/3+1/100000,(source.slope+1)/6-1/100000),
       (source.slope/3+1/100000,(source.slope+3)/6-1/100000),
       ((source.slope+1)/3+1/100000,(3*source.slope+1)/6-1/100000)])
    (returns : ∀ level ∈ innerTarget denominator outerIntervals,
      TwoReturns (fun digit => (offsets digit : ℝ)/denominator)
        (innerTarget denominator innerIntervals) maximumDepth level) :
    0 < dimH (intersection (source.exponent : ℝ) (1/3)) := by
  have outer_identity : innerTarget denominator outerIntervals = switchLevels source.slope :=
    (scaled_intervals_eq denominator positive outerIntervals _ outer_exact).trans
      (rational_switch_intervals source.slope)
  have inner_identity : innerTarget denominator innerIntervals =
      trimmedSwitchLevels source.slope (1/100000) := by
    have identity := (scaled_intervals_eq denominator positive innerIntervals _ inner_exact).trans
      (rational_trimmed_switch_intervals source.slope (1/100000))
    norm_num at identity
    exact identity
  rw [outer_identity,inner_identity,
    geometricOffset_eq_certified source.slope denominator offsets offsets_exact] at returns
  obtain ⟨atlas,atlas_depth,atlas_margin⟩ := finiteReturnAtlas_of_twoReturns source.slope (1/100000)
    maximumDepth (switchLevels source.slope) (trimmedSwitchLevels source.slope (1/100000))
    (by norm_num) returns
    (fun returned membership value close => trimmed_switch_robust _ _ _ _ membership close)
  apply source.positive_dimension valid _ atlas (atlas_depth.trans depth_matches.symm) atlas_margin
    (source.intercept_mem_switch valid)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,slope_lower,slope_upper,_⟩ := valid
  have lower : (1:ℝ) < source.slope := by exact_mod_cast slope_lower
  have upper : (source.slope : ℝ) < 3 := by exact_mod_cast slope_upper
  exact switch_levels_bounded _ lower upper

end LambdaCantor.Integer.Exceptional
