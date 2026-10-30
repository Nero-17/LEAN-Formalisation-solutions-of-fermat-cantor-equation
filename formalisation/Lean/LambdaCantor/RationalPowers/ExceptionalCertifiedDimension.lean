import LambdaCantor.RationalPowers.ExceptionalDimension

noncomputable section
namespace LambdaCantor.RationalPowers.Exceptional
open LambdaCantor.Integer.Exceptional

/-- A finite rational source check and two finite integer DAG checks imply
positive dimension for the actual real-power Cantor intersection. In
particular, the input contains no return-word or dimension oracle. -/
theorem certified_source_positive_dimension (source : PowerSource) (valid : source.Valid)
    (denominator : ℤ) (denominator_positive : 0 < denominator) (offsets : Fin 4 → ℤ)
    (outerIntervals innerIntervals : List (ℤ × ℤ)) (nodes : Array Node)
    (roots : List ℕ) (maximumDepth : ℕ)
    (depth_matches : source.returnDepth = maximumDepth)
    (offsets_exact : ∀ digit : Fin 4, (offsets digit : ℚ)/denominator =
      match digit.val with | 0 => 0 | 1 => 1 | 2 => source.slope | _ => source.slope+1)
    (outer_exact : outerIntervals.map (fun interval =>
      ((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator)) =
      [(1/3,(source.slope+1)/6),(source.slope/3,(source.slope+3)/6),
        ((source.slope+1)/3,(3*source.slope+1)/6)])
    (inner_exact : innerIntervals.map (fun interval =>
      ((interval.1 : ℚ)/denominator,(interval.2 : ℚ)/denominator)) =
      [(1/3+source.margin,(source.slope+1)/6-source.margin),
        (source.slope/3+source.margin,(source.slope+3)/6-source.margin),
        ((source.slope+1)/3+source.margin,(3*source.slope+1)/6-source.margin)])
    (certificate_checked : checkCertificate denominator offsets innerIntervals nodes = true)
    (roots_checked : checkRoots outerIntervals nodes roots maximumDepth = true) :
    0 < dimH (intersection (source.exponent : ℝ) (1/3)) := by
  have returns := checked_roots_sound denominator offsets innerIntervals outerIntervals nodes roots
    maximumDepth certificate_checked roots_checked
  have outer_identity : innerTarget denominator outerIntervals = switchLevels source.slope :=
    (scaled_intervals_eq denominator denominator_positive outerIntervals _ outer_exact).trans
      (rational_switch_intervals source.slope)
  have inner_identity : innerTarget denominator innerIntervals =
      trimmedSwitchLevels source.slope source.margin :=
    (scaled_intervals_eq denominator denominator_positive innerIntervals _ inner_exact).trans
      (rational_trimmed_switch_intervals source.slope source.margin)
  rw [outer_identity,inner_identity,geometricOffset_eq_certified source.slope denominator offsets offsets_exact]
    at returns
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,margin_positive⟩ := valid.1
  have margin_real : (0 : ℝ) < source.margin := by exact_mod_cast margin_positive
  obtain ⟨atlas,atlas_depth,atlas_margin⟩ := finiteReturnAtlas_of_twoReturns source.slope source.margin
    maximumDepth (switchLevels source.slope) (trimmedSwitchLevels source.slope source.margin)
    margin_real returns (fun returned member value close => trimmed_switch_robust _ _ _ _ member close)
  exact source.positive_dimension valid atlas (atlas_depth.trans depth_matches.symm) atlas_margin

end LambdaCantor.RationalPowers.Exceptional
