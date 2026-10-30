import LambdaCantor.Integer.NearAxisSource
import LambdaCantor.Integer.FermatTangent

namespace LambdaCantor.Integer

noncomputable def nearAxisPhysical (n d p q k P Q : ℕ) (point : ℝ × ℝ) : ℝ × ℝ :=
  ((1/3 : ℝ)^k*((P+point.1)/3^p),
    1-(1/3 : ℝ)^(n*k+d)*((Q+1-point.2)/3^q))

theorem nearAxisPhysical_injective (n d p q k P Q : ℕ) :
    Function.Injective (nearAxisPhysical n d p q k P Q) := by
  intro first second equality
  have firstEqual := congrArg Prod.fst equality
  have secondEqual := congrArg Prod.snd equality
  unfold nearAxisPhysical at firstEqual secondEqual
  dsimp only at firstEqual secondEqual
  have firstScale : (1/3 : ℝ)^k ≠ 0 := by positivity
  have secondScale : (1/3 : ℝ)^(n*k+d) ≠ 0 := by positivity
  apply Prod.ext
  · have divided := mul_left_cancel₀ firstScale firstEqual
    have summed := (div_left_inj' (by positivity : (3 : ℝ)^p ≠ 0)).1 divided
    linarith
  · have divided : ((Q : ℝ)+1-first.2)/3^q = ((Q : ℝ)+1-second.2)/3^q := by
      apply mul_left_cancel₀ secondScale
      linarith
    have summed := (div_left_inj' (by positivity : (3 : ℝ)^q ≠ 0)).1 divided
    linarith

theorem near_axis_fibre_physical (n d p q k P Q : ℕ)
    (positiveP : 0 < P) (positiveQ : 0 < Q) (boundQ : Q+1 ≤ 3^q)
    (small : (1/3 : ℝ)^(n*k+d) < 1)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q)))
    (point : ℝ × ℝ) (member : point ∈ Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0) :
    0 < (nearAxisPhysical n d p q k P Q point).1 ∧
    0 < (nearAxisPhysical n d p q k P Q point).2 ∧
    (nearAxisPhysical n d p q k P Q point).1^n+
      (nearAxisPhysical n d p q k P Q point).2^n = 1 := by
  have firstMember : point.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.1
  have secondMember : point.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.2
  have firstBounds := _root_.cantorSet_subset_unitInterval firstMember
  have secondBounds := _root_.cantorSet_subset_unitInterval secondMember
  have positivePReal : (0 : ℝ) < P := by exact_mod_cast positiveP
  have uPositive : 0 < ((P : ℝ)+point.1)/3^p :=
    div_pos (by linarith [firstBounds.1]) (by positivity)
  have vUpper : ((Q : ℝ)+1-point.2)/3^q ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (3 : ℝ)^q)).2
    have castBound : (Q : ℝ)+1 ≤ (3 : ℝ)^q := by exact_mod_cast boundQ
    linarith [secondBounds.1]
  refine ⟨by dsimp [nearAxisPhysical]; positivity,?_,?_⟩
  · have multiplied := mul_le_mul_of_nonneg_left vUpper
      (show (0 : ℝ) ≤ (1/3 : ℝ)^(n*k+d) by positivity)
    dsimp [nearAxisPhysical]
    nlinarith
  · exact near_axis_log_zero_fermat n d p q k P Q point.1 point.2
      uPositive (positiveResidual _ secondBounds) member.2

/-- An uncountable normalized exact source yields an irrational physical
tangent. The injectivity used here is proved from the Fermat equation. -/
theorem near_axis_irrational_tangent (n d p q k P Q : ℕ) (exponent : 3 ≤ n)
    (positiveP : 0 < P) (positiveQ : 0 < Q) (boundQ : Q+1 ≤ 3^q)
    (small : (1/3 : ℝ)^(n*k+d) < 1)
    (positiveResidual : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < ((Q+1-y)/3^q)*fermatQuotient n ((1/3 : ℝ)^(n*k+d)*((Q+1-y)/3^q)))
    (uncountable : ¬ (Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0).Countable) :
    ∃ point ∈ Classical.cantorLevel (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0,
      ∀ rational : ℚ, fermatTangent n (nearAxisPhysical n d p q k P Q point) ≠ (rational : ℝ) := by
  apply exists_irrational_tangent _ uncountable
    (fun point => fermatTangent n (nearAxisPhysical n d p q k P Q point))
  intro first firstMember second secondMember equal
  apply nearAxisPhysical_injective n d p q k P Q
  apply fermat_tangent_injective n (by omega)
    (nearAxisPhysical n d p q k P Q '' Classical.cantorLevel
      (nearAxisLog n d p q P Q ((1/3 : ℝ)^(n*k+d))) 0)
  · intro point member
    obtain ⟨preimage,member,rfl⟩ := member
    have facts := near_axis_fibre_physical n d p q k P Q positiveP positiveQ boundQ
      small positiveResidual preimage member
    exact ⟨facts.1,facts.2.1⟩
  · intro point member
    obtain ⟨preimage,member,rfl⟩ := member
    exact (near_axis_fibre_physical n d p q k P Q positiveP positiveQ boundQ
      small positiveResidual preimage member).2.2
  · exact ⟨first,firstMember,rfl⟩
  · exact ⟨second,secondMember,rfl⟩
  · exact equal

/-- Unconditional transfer from the finite strict source hypotheses to an
irrational tangent on an actual positive Cantor point of the Fermat curve. -/
theorem strict_log_source_actual_irrational_tangent (n d p q P Q : ℕ) (a b : ℝ)
    (exponent : 3 ≤ n) (positiveP : 0 < P) (positiveQ : 0 < Q)
    (prefixP : ternaryPrefix P p = true) (prefixQ : ternaryPrefix Q q = true)
    (boundQ : Q+1 ≤ 3^q)
    (lowerBand : 1 < a) (upperBand : b < 3) (positiveB : 0 < b)
    (bandGood : ∀ slope : ℝ, a < slope → slope < b → GoodSlope slope)
    (lowerRatio : a/Q < (n : ℝ)/(P+1))
    (upperRatio : (n : ℝ)/P < b/(Q+1))
    (lowerCorner : nearAxisLog n d p q P Q 0 0 0 < 0)
    (upperCorner : 0 < nearAxisLog n d p q P Q 0 1 1) :
    ∃ point : ℝ × ℝ, point.1 ∈ _root_.cantorSet ∧ point.2 ∈ _root_.cantorSet ∧
      0 < point.1 ∧ 0 < point.2 ∧ point.1^n+point.2^n=1 ∧
      ∀ rational : ℚ, fermatTangent n point ≠ (rational : ℝ) := by
  obtain ⟨k,_,_,_,uncountable,small,residual,_⟩ := near_axis_perfect_source n d p q P Q a b
    exponent positiveP positiveQ boundQ lowerBand upperBand positiveB bandGood
    lowerRatio upperRatio lowerCorner upperCorner
  obtain ⟨point,member,irrational⟩ := near_axis_irrational_tangent n d p q k P Q
    exponent positiveP positiveQ boundQ small residual uncountable
  have firstMember : point.1 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.1
  have secondMember : point.2 ∈ _root_.cantorSet := by
    rw [← cantorSet_third_eq]; exact member.1.2
  have cylinders := near_axis_physical_cylinders n d k P Q p q prefixP prefixQ
    point.1 point.2 firstMember secondMember
  have facts := near_axis_fibre_physical n d p q k P Q positiveP positiveQ boundQ
    small residual point member
  exact ⟨nearAxisPhysical n d p q k P Q point,cylinders.1,cylinders.2,
    facts.1,facts.2.1,facts.2.2,irrational⟩

end LambdaCantor.Integer
