import LambdaCantor.Integer.ExceptionalCertificate

namespace LambdaCantor.Integer.Exceptional

/-- Check a half-open range of global node indices. Every lookup still uses
the full certificate array, including references into earlier ranges. -/
def checkNodeRange (offsets : Fin 4 → ℤ) (innerIntervals : List (ℤ × ℤ))
    (nodes : Array Node) (lower upper : ℕ) : Bool :=
  (List.range (upper - lower)).all
    (fun offset => decide (nodeValid offsets innerIntervals nodes (lower + offset)))

def checkRangeCover (size : ℕ) (ranges : List (ℕ × ℕ)) : Bool :=
  (List.range size).all (fun index =>
    ranges.any (fun bounds => decide (bounds.1 ≤ index ∧ index < bounds.2)))

theorem checkNodeRange_sound (offsets : Fin 4 → ℤ) (innerIntervals : List (ℤ × ℤ))
    (nodes : Array Node) (lower upper : ℕ)
    (checked : checkNodeRange offsets innerIntervals nodes lower upper = true)
    (index : ℕ) (lower_bound : lower ≤ index) (upper_bound : index < upper) :
    nodeValid offsets innerIntervals nodes index := by
  simp only [checkNodeRange, List.all_eq_true, decide_eq_true_eq] at checked
  have offset_bound : index - lower < upper - lower := by omega
  have index_eq : lower + (index - lower) = index := by omega
  simpa only [index_eq] using checked (index - lower) (List.mem_range.mpr offset_bound)

/-- Chunked native checks imply exactly the existing monolithic checker.
No range is trusted to be disjoint, ordered or complete without checking. -/
theorem checkCertificate_of_checkedRanges (denominator : ℤ) (positive : 0 < denominator)
    (offsets : Fin 4 → ℤ) (innerIntervals : List (ℤ × ℤ)) (nodes : Array Node)
    (ranges : List (ℕ × ℕ)) (covered : checkRangeCover nodes.size ranges = true)
    (checked : ∀ bounds ∈ ranges,
      checkNodeRange offsets innerIntervals nodes bounds.1 bounds.2 = true) :
    checkCertificate denominator offsets innerIntervals nodes = true := by
  simp only [checkRangeCover, List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at covered
  simp only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨positive, ?_⟩
  intro index member
  obtain ⟨bounds, range_member, lower_bound, upper_bound⟩ := covered index member
  exact checkNodeRange_sound offsets innerIntervals nodes bounds.1 bounds.2
    (checked bounds range_member) index lower_bound upper_bound

end LambdaCantor.Integer.Exceptional
