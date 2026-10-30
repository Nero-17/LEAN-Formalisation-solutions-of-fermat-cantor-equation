import LambdaCantor.Integer.AffineAddresses

namespace LambdaCantor.Integer

theorem affine_isolated_rational (r level : ℝ) (good : GoodSlope r)
    (point : affineFibre r level) (isolated : IsOpen ({point} : Set (affineFibre r level))) :
    ∃ x y : ℚ, (x : ℝ)=point.val.1 ∧ (y : ℝ)=point.val.2 := by
  have firstMember : point.val.1 ∈ cantorSet (1/3) := by
    rw [cantorSet_third_eq]
    exact point.property.1.1
  have secondMember : point.val.2 ∈ cantorSet (1/3) := by
    rw [cantorSet_third_eq]
    exact point.property.1.2
  obtain ⟨first,firstValue⟩ := firstMember
  obtain ⟨second,secondValue⟩ := secondMember
  obtain ⟨radius,positive,ball⟩ := Metric.isOpen_iff.mp isolated point (by simp)
  obtain ⟨⟨x,xValue⟩,⟨y,yValue⟩⟩ := isolated_affine_addresses_rational r good first second
    radius positive (by
      intro other member close
      have levelEquation : (r*point.val.1+point.val.2)/2=level := point.property.2
      have otherMember : other ∈ affineFibre r level := by
        simpa only [firstValue,secondValue,levelEquation] using member
      have near : (⟨other,otherMember⟩ : affineFibre r level) ∈ Metric.ball point radius := by
        change dist other point.val < radius
        have pointEquation : (address (1/3) first,address (1/3) second)=point.val :=
          Prod.ext firstValue secondValue
        simpa only [pointEquation] using close
      have equal : (⟨other,otherMember⟩ : affineFibre r level)=point :=
        Set.mem_singleton_iff.mp (ball near)
      have equalValue := congrArg Subtype.val equal
      exact equalValue.trans (Prod.ext firstValue secondValue).symm)
  exact ⟨x,y,xValue.trans firstValue,yValue.trans secondValue⟩

/-- Unconditional affine-fibre conclusion for the five graph-certified bands.
Every switch level at an irrational slope has uncountably many Cantor points. -/
theorem irrational_good_switch_uncountable (r level : ℝ) (good : GoodSlope r)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) (switch : level ∈ switchSet r) :
    ¬ (affineFibre r level).Countable := by
  obtain ⟨lower,upper⟩ := goodSlope_between_one_three good
  exact switch_fibre_uncountable r level lower.le upper.le irrational switch
    (affine_isolated_rational r level good)

end LambdaCantor.Integer
