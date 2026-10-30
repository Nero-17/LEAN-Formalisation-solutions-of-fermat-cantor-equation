import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Compact

noncomputable section
namespace LambdaCantor.Last.ExternalNewhouse

/-- A completely specified binary Cantor construction. In particular, exact
limit-set equality and vanishing mesh are obligations of every application. -/
structure BinaryGapPresentation (set : Set ℝ) where
  left : List Bool → ℝ
  right : List Bool → ℝ
  node_order : ∀ word, left word < right word
  left_coherent : ∀ word, left (word ++ [false]) = left word
  right_coherent : ∀ word, right (word ++ [true]) = right word
  children_order : ∀ word,
    left word < right (word ++ [false]) ∧
      right (word ++ [false]) < left (word ++ [true]) ∧
      left (word ++ [true]) < right word
  limit_set : set = {point | ∀ depth : ℕ, ∃ word : List Bool,
    word.length = depth ∧ point ∈ Set.Icc (left word) (right word)}
  mesh : ∀ epsilon : ℝ, 0 < epsilon → ∃ depth : ℕ,
    ∀ word : List Bool, depth ≤ word.length → right word - left word < epsilon

def BinaryGapPresentation.bridgeBound {set : Set ℝ}
    (presentation : BinaryGapPresentation set) (thickness : ℝ) : Prop :=
  ∀ word : List Bool,
    thickness * (presentation.left (word ++ [true]) -
      presentation.right (word ++ [false])) ≤
        presentation.right (word ++ [false]) - presentation.left word ∧
    thickness * (presentation.left (word ++ [true]) -
      presentation.right (word ++ [false])) ≤
        presentation.right word - presentation.left (word ++ [true])

/-- Complementary intervals include both unbounded gaps. -/
def NotContainedInGap (first second : Set ℝ) : Prop :=
  ∀ interval : Set ℝ, interval.OrdConnected → interval ⊆ secondᶜ → ¬ first ⊆ interval

/-- Classical Newhouse Gap Lemma in its binary defining-sequence formulation.

Source: Newhouse (1979), printed pp.106--108, Lemma 4 and Remark 2,
https://numdam.org/item/PMIHES_1979__50__101_0.pdf . The definition on p.106
takes the supremum over all gap-removal defining sequences, without sorting
gaps by size. Enumerating these binary node gaps ancestor first gives such a
sequence; its two bridge lengths are the immediate child widths. Positive
node widths, strict children, exact limit equality and vanishing mesh ensure
that the represented set is a nonempty compact perfect Cantor set. Thus the
bridge bounds give lower bounds on Newhouse thickness. Remark 2 permits open
gap noncontainment for the intersection conclusion used here. No finite-stage
interior conclusion is asserted. This statement is about arbitrary real Cantor
constructions; it has no contraction parameter, power curve, or dimension claim. -/
axiom binary_defining_sequence_gap_lemma
    (first second : Set ℝ)
    (first_presentation : BinaryGapPresentation first)
    (second_presentation : BinaryGapPresentation second)
    (first_bound second_bound : ℝ)
    (first_positive : 0 < first_bound) (second_positive : 0 < second_bound)
    (product_large : 1 < first_bound * second_bound)
    (first_bridges : first_presentation.bridgeBound first_bound)
    (second_bridges : second_presentation.bridgeBound second_bound)
    (first_not_in_gap : NotContainedInGap first second)
    (second_not_in_gap : NotContainedInGap second first) :
    (first ∩ second).Nonempty

end LambdaCantor.Last.ExternalNewhouse
