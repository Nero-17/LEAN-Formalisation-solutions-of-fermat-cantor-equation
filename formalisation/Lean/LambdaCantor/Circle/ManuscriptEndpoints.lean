import LambdaCantor.Circle.ParameterConsequences
import LambdaCantor.First.RootsMain

noncomputable section
open MeasureTheory
namespace LambdaCantor.Circle

/-- The circle has positive-dimensional parameters of positive Lebesgue
measure in every right neighbourhood of onset. -/
theorem circle_positive_measure (epsilon : ℝ) (epsilon_positive : 0 < epsilon) :
    0 < volume {ratio : ℝ | ratio ∈ Set.Ioo onset (onset + epsilon) ∧
      0 < dimH (intersection 2 ratio)} :=
  circle_positive_measure_of_rootFibreConclusion
    (fun data => First.Roots.root_fibres data) epsilon epsilon_positive

/-- The first circle transition is the exact geometric onset. -/
theorem circle_onset : firstTransition 2 = onset :=
  circle_onset_of_rootFibreConclusion (fun data => First.Roots.root_fibres data)

/-- The circle onset and last transition are strictly separated. -/
theorem circle_known_separation :
    firstTransition 2 = onset ∧ onset < lastTransition 2 :=
  circle_known_separation_of_rootFibreConclusion (fun data => First.Roots.root_fibres data)

end LambdaCantor.Circle

#print axioms LambdaCantor.Circle.circle_positive_measure
#print axioms LambdaCantor.Circle.circle_onset
#print axioms LambdaCantor.Circle.circle_known_separation
