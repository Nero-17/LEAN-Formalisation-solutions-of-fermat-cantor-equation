import LambdaCantor.Integer.PhaseNaturalShift
import LambdaCantor.Integer.LogCertificateTransfer

namespace LambdaCantor.Integer

noncomputable def centeredSourceLower (n : ℕ) (center : ℝ) (source : LogSourceData) : ℝ :=
  (Real.log ((source.Q : ℝ)/3^source.q)+
    (n : ℝ)*Real.log (center/((source.P+1)/3^source.p)))/Real.log 3

noncomputable def centeredSourceUpper (n : ℕ) (center : ℝ) (source : LogSourceData) : ℝ :=
  (Real.log (((source.Q : ℝ)+1)/3^source.q)+
    (n : ℝ)*Real.log (center/((source.P : ℝ)/3^source.p)))/Real.log 3

/-- Full-circle strict phase coverage supplies a genuine finite logarithmic
source, with natural depth rather than an unchecked signed shift. The resulting
object is the input to `geometry_log_source_normalized_transfer`. -/
theorem phase_cover_to_log_source (n : ℕ) (positiveN : 0 < n) (center : ℝ)
    (centerPositive : 0 < center)
    (covered : ∀ phase ∈ Set.Icc (0 : ℝ) 1, ∃ source : LogSourceData, ∃ shift : ℤ,
      source.GeometryChecked n ∧ 1 ≤ (n : ℝ)*((source.Q : ℝ)/3^source.q) ∧
      centeredSourceLower n center source < phase+shift ∧
      phase+shift < centeredSourceUpper n center source) :
    ∃ source : LogSourceData, source.GeometryChecked n ∧
      (n : ℝ)*Real.log ((source.P : ℝ)/3^source.p)-Real.log ((source.Q+1)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 < 0 ∧
      0 < (n : ℝ)*Real.log ((source.P+1)/3^source.p)-Real.log ((source.Q : ℝ)/3^source.q)-
        Real.log n+(source.d : ℝ)*Real.log 3 := by
  obtain ⟨source,depth,valid,lower,upper⟩ := phase_cover_natural_shift
    (fun source : LogSourceData => source.GeometryChecked n ∧
      1 ≤ (n : ℝ)*((source.Q : ℝ)/3^source.q))
    (centeredSourceLower n center) (centeredSourceUpper n center)
    (((n : ℝ)*Real.log center-Real.log n)/Real.log 3)
    (by
      intro phase phaseBounds
      obtain ⟨source,shift,geometry,product,lower,upper⟩ := covered phase phaseBounds
      exact ⟨source,shift,⟨geometry,product⟩,lower,upper⟩)
    (by
      intro source valid
      have positiveP := valid.1.2.1
      have positiveQ := valid.1.2.2.1
      have boundP := valid.1.2.2.2.2.2.1
      apply centered_log_phase_lower_ge_rotation n center _ _
        (by exact_mod_cast positiveN) centerPositive (by positivity) _ (by positivity) valid.2
      apply (div_le_one (by positivity : (0 : ℝ) < (3 : ℝ)^source.p)).2
      exact_mod_cast boundP)
  have positiveP := valid.1.2.1
  have corners := centered_log_phase_corners n depth center
    ((source.P : ℝ)/3^source.p) ((source.P+1)/3^source.p)
    ((source.Q : ℝ)/3^source.q) ((source.Q+1)/3^source.q)
    positiveN centerPositive (by positivity) (by positivity) lower upper
  refine ⟨{source with d := depth},?_,corners.1,corners.2⟩
  simpa only [LogSourceData.GeometryChecked] using valid.1

end LambdaCantor.Integer
