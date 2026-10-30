import LambdaCantor.Integer.NearAxisTangent

namespace LambdaCantor.Integer

theorem normalized_tangent_product (n d p q k P Q : ℕ) (positiveN : 0 < n)
    (point : ℝ × ℝ) (uPositive : 0 < (P+point.1)/(3 : ℝ)^p)
    (yPositive : 0 < (nearAxisPhysical n d p q k P Q point).2)
    (residualPositive : 0 < ((Q+1-point.2)/3^q)*
      fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-point.2)/3^q)))
    (equation : nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d)) point.1 point.2 = 0) :
    (nearAxisHorizontal n P point.1/nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2)*
      fermatTangent n (nearAxisPhysical n d p q k P Q point) =
        (3 : ℝ)^q*3^d/(3^p*((1/3 : ℝ)^k)^(n-1)) := by
  have residual := nearAxisLog_zero_residual n d p q P Q ((1/3 : ℝ)^(n*k+d))
    point.1 point.2 uPositive residualPositive equation
  have numeratorPositive : 0 < (P : ℝ)+point.1 :=
    (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < (3 : ℝ)^p)).1 uPositive
  have numeratorNonzero := ne_of_gt numeratorPositive
  have nNonzero : (n : ℝ) ≠ 0 := by positivity
  have yNonzero : 1-(1/3 : ℝ)^(n*k+d)*((Q+1-point.2)/3^q) ≠ 0 := ne_of_gt yPositive
  unfold nearAxisHorizontal nearAxisVertical fermatLogDerivative fermatTangent nearAxisPhysical
  dsimp only
  rw [← residual]
  have exponent : n = (n-1)+1 := by omega
  rw [show (((P : ℝ)+point.1)/3^p)^n =
      (((P : ℝ)+point.1)/3^p)^(n-1)*(((P : ℝ)+point.1)/3^p) by
        conv_lhs => rw [exponent]
        rw [pow_succ]]
  simp only [mul_pow,div_pow]
  field_simp [nNonzero,numeratorNonzero,yNonzero]
  <;> ring_nf
  all_goals
    simp only [inv_pow]
    apply inv_mul_cancel₀
    apply pow_ne_zero
    convert yNonzero using 1 <;>
      simp only [one_div,inv_pow,pow_add] <;> field_simp <;> ring

theorem near_axis_normalized_tangent_injective (n d p q k P Q : ℕ) (exponent : 3 ≤ n)
    (positiveP : 0 < P) (positiveQ : 0 < Q) (boundQ : Q+1 ≤ 3^q)
    (small : (1/3 : ℝ)^(n*k+d) < 1)
    (residual : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < ((Q+1-y)/3^q)*
      fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q))) :
    Set.InjOn (fun point : ℝ × ℝ => nearAxisHorizontal n P point.1/
      nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2)
      (Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0) := by
  intro first firstMember second secondMember equality
  dsimp only at equality
  have facts (point : ℝ × ℝ) (member : point ∈ Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0) :=
    near_axis_fibre_physical n d p q k P Q positiveP positiveQ boundQ small residual point member
  have product (point : ℝ × ℝ) (member : point ∈ Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0) :
      (nearAxisHorizontal n P point.1/nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2)*
        fermatTangent n (nearAxisPhysical n d p q k P Q point) =
          (3 : ℝ)^q*3^d/(3^p*((1/3 : ℝ)^k)^(n-1)) := by
    have firstCantor : point.1 ∈ _root_.cantorSet := by
      rw [← cantorSet_third_eq]; exact member.1.1
    have secondCantor : point.2 ∈ _root_.cantorSet := by
      rw [← cantorSet_third_eq]; exact member.1.2
    have positivePReal : (0 : ℝ) < P := by exact_mod_cast positiveP
    have firstBounds := _root_.cantorSet_subset_unitInterval firstCantor
    exact normalized_tangent_product n d p q k P Q (by omega) point
      (div_pos (by linarith [firstBounds.1]) (by positivity)) (facts point member).2.1
      (residual _ (_root_.cantorSet_subset_unitInterval secondCantor)) member.2
  have firstProduct := product first firstMember
  have secondProduct := product second secondMember
  have constantNonzero : (3 : ℝ)^q*3^d/(3^p*((1/3 : ℝ)^k)^(n-1)) ≠ 0 := by positivity
  have slopeNonzero : nearAxisHorizontal n P first.1/
      nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) first.2 ≠ 0 := by
    intro zero
    rw [zero,zero_mul] at firstProduct
    exact constantNonzero firstProduct.symm
  have tangentEqual : fermatTangent n (nearAxisPhysical n d p q k P Q first) =
      fermatTangent n (nearAxisPhysical n d p q k P Q second) := by
    apply mul_left_cancel₀ slopeNonzero
    rw [firstProduct,equality,secondProduct]
  apply nearAxisPhysical_injective n d p q k P Q
  apply fermat_tangent_injective n (by omega)
    (nearAxisPhysical n d p q k P Q '' Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0)
  · intro point member
    obtain ⟨preimage,member,rfl⟩ := member
    exact ⟨(facts preimage member).1,(facts preimage member).2.1⟩
  · intro point member
    obtain ⟨preimage,member,rfl⟩ := member
    exact (facts preimage member).2.2
  · exact ⟨first,firstMember,rfl⟩
  · exact ⟨second,secondMember,rfl⟩
  · exact tangentEqual

theorem strict_log_source_normalized_irrational_tangent (n d p q P Q : ℕ) (a b : ℝ)
    (exponent : 3 ≤ n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (boundQ : Q+1 ≤ 3^q)
    (lowerBand : 1 < a) (upperBand : b < 3) (positiveB : 0 < b)
    (bandGood : ∀ slope : ℝ, a < slope → slope < b → GoodSlope slope)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    ∃ k : ℕ, ∃ point ∈ Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0,
      GoodSlope (nearAxisHorizontal n P point.1/
        nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2) ∧
      ∀ rational : ℚ, nearAxisHorizontal n P point.1/
        nearAxisVertical n q Q ((1/3 : ℝ)^(n*k+d)) point.2 ≠ (rational : ℝ) := by
  obtain ⟨k,_,_,_,uncountable,small,residual,slopes⟩ := near_axis_perfect_source n d p q P Q a b
    exponent positiveP positiveQ boundQ lowerBand upperBand positiveB bandGood
    lowerRatio upperRatio lowerCorner upperCorner
  obtain ⟨point,member,irrational⟩ := exists_irrational_tangent _ uncountable _
    (near_axis_normalized_tangent_injective n d p q k P Q exponent positiveP positiveQ boundQ small residual)
  have firstCantor : point.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.1
  have secondCantor : point.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.2
  exact ⟨k,point,member,(slopes _ (_root_.cantorSet_subset_unitInterval firstCantor)
    _ (_root_.cantorSet_subset_unitInterval secondCantor)).2,irrational⟩

end LambdaCantor.Integer
