import LambdaCantor.Integer.AffineRationalFibres
import LambdaCantor.Integer.UncountableBranching
import LambdaCantor.SelfSimilarity

namespace LambdaCantor.Integer

noncomputable def pairedAddress (digits : ℕ → Bool × Bool) : ℝ × ℝ :=
  (address (1/3) (fun n => (digits n).1),address (1/3) (fun n => (digits n).2))

def affineAddressFibre (r level : ℝ) : Set (ℕ → Bool × Bool) :=
  pairedAddress ⁻¹' affineFibre r level

theorem pairedAddress_injective : Function.Injective pairedAddress := by
  intro first second equal
  have firstCoordinate := congrArg Prod.fst equal
  have secondCoordinate := congrArg Prod.snd equal
  have firstDigits := address_injective (by norm_num : (0 : ℝ) < 1/3)
    (by norm_num : (1/3 : ℝ) < 1/2) firstCoordinate
  have secondDigits := address_injective (by norm_num : (0 : ℝ) < 1/3)
    (by norm_num : (1/3 : ℝ) < 1/2) secondCoordinate
  funext n
  exact Prod.ext (congrFun firstDigits n) (congrFun secondDigits n)

theorem affineAddressFibre_image (r level : ℝ) :
    pairedAddress '' affineAddressFibre r level = affineFibre r level := by
  ext point
  constructor
  · rintro ⟨digits,member,rfl⟩
    exact member
  · intro member
    have firstMember : point.1 ∈ cantorSet (1/3) := by
      rw [cantorSet_third_eq]
      exact member.1.1
    have secondMember : point.2 ∈ cantorSet (1/3) := by
      rw [cantorSet_third_eq]
      exact member.1.2
    obtain ⟨first,firstValue⟩ := firstMember
    obtain ⟨second,secondValue⟩ := secondMember
    have equal : pairedAddress (fun n => (first n,second n))=point :=
      Prod.ext firstValue secondValue
    refine ⟨fun n => (first n,second n), ?_, equal⟩
    change pairedAddress (fun n => (first n,second n)) ∈ affineFibre r level
    rwa [equal]

theorem affineAddressFibre_uncountable (r level : ℝ)
    (uncountable : ¬ (affineFibre r level).Countable) :
    ¬ (affineAddressFibre r level).Countable := by
  intro countable
  apply uncountable
  rw [← affineAddressFibre_image]
  exact countable.image pairedAddress

/-- The two-uncountable-children tree step for actual affine Cantor fibres. -/
theorem irrational_switch_addresses_branch (r level : ℝ) (good : GoodSlope r)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) (switch : level ∈ switchSet r) :
    ∃ left ∈ affineAddressFibre r level, ∃ right ∈ affineAddressFibre r level,
      ∃ depth : ℕ, (∀ j < depth, left j=right j) ∧ left depth ≠ right depth ∧
      ¬ (affineAddressFibre r level ∩
        prefixCylinder ⟨depth+1,fun j => left j.val⟩).Countable ∧
      ¬ (affineAddressFibre r level ∩
        prefixCylinder ⟨depth+1,fun j => right j.val⟩).Countable :=
  uncountable_addresses_branch (affineAddressFibre r level)
    (affineAddressFibre_uncountable r level
      (irrational_good_switch_uncountable r level good irrational switch))

end LambdaCantor.Integer
