import LambdaCantor.Integer.AffineSwitchFibres
import LambdaCantor.Integer.Feasibility
import LambdaCantor.Classical.Cylinders

namespace LambdaCantor.Integer

/-- Exact exclusive-domain bounds for a singleton affine fibre. -/
theorem singleton_fibre_exclusive (r level : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (singleton : (affineFibre r level).Subsingleton) (child : Fin 4)
    (childImage : childOffset r child/3 ≤ level ∧
      level ≤ childOffset r child/3+(r+1)/6) :
    ((lowerCoefficient child.val).1*r+(lowerCoefficient child.val).2)/6 ≤ level ∧
    level ≤ ((upperCoefficient child.val).1*r+(upperCoefficient child.val).2)/6 := by
  have notSwitch : level ∉ switchSet r := by
    intro switch
    obtain ⟨p, hp, q, hq, different⟩ := switch_fibre_nontrivial r level lower upper switch
    exact different (singleton hp hq)
  fin_cases child <;> norm_num [childOffset, lowerCoefficient, upperCoefficient] at childImage ⊢
  all_goals constructor
  all_goals by_contra fail
  all_goals apply notSwitch
  all_goals first
    | (left; left; constructor <;> linarith [childImage.1, childImage.2])
    | (left; right; constructor <;> linarith [childImage.1, childImage.2])
    | (right; constructor <;> linarith [childImage.1, childImage.2])

/-- Isolation forces every sufficiently deep normalized affine fibre to be
a singleton. The cylinder diameter tends to zero, and prefixing preserves
Cantor membership. This is specific to affine fibres and has zero Taylor error. -/
theorem isolated_affine_eventually_singleton (r : ℝ) (first second : ℕ → Bool)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (isolated : ∀ point ∈ affineFibre r
      ((r*address (1/3) first+address (1/3) second)/2),
      dist point (address (1/3) first,address (1/3) second) < radius →
        point=(address (1/3) first,address (1/3) second)) :
    ∃ start, ∀ depth ≥ start,
      (affineFibre r ((r*address (1/3) (fun j => first (j+depth))+
        address (1/3) (fun j => second (j+depth)))/2)).Subsingleton := by
  obtain ⟨start, small⟩ := Classical.cylinder_eventually_in_ball first second radius radiusPositive
  refine ⟨start, ?_⟩
  intro depth large
  have positive : 0 < (1/3 : ℝ)^depth := by positivity
  have prefixFirst := address_prefix_tail (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) first depth
  have prefixSecond := address_prefix_tail (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) second depth
  have unique : ∀ p ∈ affineFibre r ((r*address (1/3) (fun j => first (j+depth))+
        address (1/3) (fun j => second (j+depth)))/2),
      p=(address (1/3) (fun j => first (j+depth)),
        address (1/3) (fun j => second (j+depth))) := by
    intro p hp
    have firstMember : p.1 ∈ cantorSet (1/3) := by
      rw [cantorSet_third_eq]
      exact hp.1.1
    have secondMember : p.2 ∈ cantorSet (1/3) := by
      rw [cantorSet_third_eq]
      exact hp.1.2
    have equal := isolated
      (prefixValue (1/3) first depth+(1/3 : ℝ)^depth*p.1,
        prefixValue (1/3) second depth+(1/3 : ℝ)^depth*p.2) (by
      constructor
      · constructor
        · rw [← cantorSet_third_eq]
          exact Classical.prefix_cantor_embedding first depth firstMember
        · rw [← cantorSet_third_eq]
          exact Classical.prefix_cantor_embedding second depth secondMember
      · change (r*(prefixValue (1/3) first depth+(1/3 : ℝ)^depth*p.1)+
          (prefixValue (1/3) second depth+(1/3 : ℝ)^depth*p.2))/2 = _
        have value := hp.2
        change (r*p.1+p.2)/2 = _ at value
        have scaled := congrArg (fun value : ℝ => (1/3 : ℝ)^depth*value) value
        rw [prefixFirst, prefixSecond]
        nlinarith [scaled])
      (small depth large p.1 p.2
        (_root_.cantorSet_subset_unitInterval hp.1.1)
        (_root_.cantorSet_subset_unitInterval hp.1.2))
    have equalFirst := congrArg Prod.fst equal
    have equalSecond := congrArg Prod.snd equal
    apply Prod.ext
    · change prefixValue (1/3) first depth+(1/3 : ℝ)^depth*p.1 =
        address (1/3) first at equalFirst
      rw [prefixFirst] at equalFirst
      nlinarith
    · change prefixValue (1/3) second depth+(1/3 : ℝ)^depth*p.2 =
        address (1/3) second at equalSecond
      rw [prefixSecond] at equalSecond
      nlinarith
  intro p hp q hq
  exact (unique p hp).trans (unique q hq).symm

end LambdaCantor.Integer
