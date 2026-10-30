import LambdaCantor.Certificates.IntegerLogSourceDefinition

namespace LambdaCantor.Integer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Recomputed exact refinement of official companion v1.0.0; depth 3.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_4 : ∃ source : LogSourceData, source.Valid 4 := by
  refine ⟨{ d := 2, P := 4860, Q := 494, p := 8, q := 6, band := ⟨9, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 0.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_5 : ∃ source : LogSourceData, source.Valid 5 := by
  refine ⟨{ d := 2, P := 216, Q := 26, p := 5, q := 3, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 1.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_6 : ∃ source : LogSourceData, source.Valid 6 := by
  refine ⟨{ d := 2, P := 216, Q := 20, p := 5, q := 3, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 1.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_7 : ∃ source : LogSourceData, source.Valid 7 := by
  refine ⟨{ d := 2, P := 222, Q := 18, p := 5, q := 3, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 0.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_8 : ∃ source : LogSourceData, source.Valid 8 := by
  refine ⟨{ d := 2, P := 2124, Q := 216, p := 7, q := 5, band := ⟨5, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 0.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_11 : ∃ source : LogSourceData, source.Valid 11 := by
  refine ⟨{ d := 3, P := 2000, Q := 74, p := 7, q := 4, band := ⟨9, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 1.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_12 : ∃ source : LogSourceData, source.Valid 12 := by
  refine ⟨{ d := 5, P := 566, Q := 26, p := 6, q := 3, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 1.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_13 : ∃ source : LogSourceData, source.Valid 13 := by
  refine ⟨{ d := 5, P := 15230, Q := 486, p := 9, q := 6, band := ⟨9, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 1.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_14 : ∃ source : LogSourceData, source.Valid 14 := by
  refine ⟨{ d := 6, P := 4916, Q := 222, p := 8, q := 5, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 0.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_15 : ∃ source : LogSourceData, source.Valid 15 := by
  refine ⟨{ d := 4, P := 216, Q := 8, p := 5, q := 2, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 0.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_16 : ∃ source : LogSourceData, source.Valid 16 := by
  refine ⟨{ d := 3, P := 234, Q := 8, p := 5, q := 2, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 1.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_17 : ∃ source : LogSourceData, source.Valid 17 := by
  refine ⟨{ d := 3, P := 704, Q := 24, p := 6, q := 3, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 2.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_18 : ∃ source : LogSourceData, source.Valid 18 := by
  refine ⟨{ d := 3, P := 2106, Q := 62, p := 7, q := 4, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 0.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_19 : ∃ source : LogSourceData, source.Valid 19 := by
  refine ⟨{ d := 3, P := 704, Q := 20, p := 6, q := 3, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 1.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_20 : ∃ source : LogSourceData, source.Valid 20 := by
  refine ⟨{ d := 3, P := 708, Q := 20, p := 6, q := 3, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

/-- Recomputed exact refinement of official companion v1.0.0; depth 0.
The previous polynomial-axis slope check is not used. -/
theorem refined_log_source_21 : ∃ source : LogSourceData, source.Valid 21 := by
  refine ⟨{ d := 3, P := 236, Q := 6, p := 5, q := 2, band := ⟨7, by decide⟩ }, ?_⟩
  decide +kernel

end LambdaCantor.Integer
