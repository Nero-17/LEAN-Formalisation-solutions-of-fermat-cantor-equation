import LambdaCantor.RationalPowers.RealNearAxisUniform
import LambdaCantor.RationalPowers.RealTangent
import LambdaCantor.Integer.TernaryPrefixSoundness
import LambdaCantor.Last.AffineRectangleEmbedding
import LambdaCantor.Classical.GeneralCoverLocal
import LambdaCantor.Classical.GeneralEventualIsolation
import LambdaCantor.Last.ReturnWords
import Mathlib.Tactic.FieldSimp

noncomputable section
namespace LambdaCantor.RationalPowers
open Last Integer
open scoped NNReal

def realNearAxisPhysical (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  ((1/3 : ℝ)^firstDepth*((horizontal+point.1)/(3 : ℝ)^horizontalDepth),
    1-(1/3 : ℝ)^secondDepth*((vertical+1-point.2)/(3 : ℝ)^verticalDepth))

theorem realNearAxisPhysical_antilipschitz
    (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ) :
    ∃ bound : ℝ≥0, AntilipschitzWith bound
      (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical) := by
  have affine := affineRectangleEmbedding_antilipschitz
    (by positivity : 0 < (1/3 : ℝ)^firstDepth/(3 : ℝ)^horizontalDepth)
    (by positivity : 0 < (1/3 : ℝ)^secondDepth/(3 : ℝ)^verticalDepth)
    ((1/3 : ℝ)^firstDepth*((horizontal : ℝ)/(3 : ℝ)^horizontalDepth))
    (1-(1/3 : ℝ)^secondDepth*((vertical+1 : ℝ)/(3 : ℝ)^verticalDepth))
  have physical_eq :
      realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical =
      affineRectangleEmbedding
        ((1/3 : ℝ)^firstDepth*((horizontal : ℝ)/(3 : ℝ)^horizontalDepth))
        ((1/3 : ℝ)^firstDepth/(3 : ℝ)^horizontalDepth)
        (1-(1/3 : ℝ)^secondDepth*((vertical+1 : ℝ)/(3 : ℝ)^verticalDepth))
        ((1/3 : ℝ)^secondDepth/(3 : ℝ)^verticalDepth) := by
    funext point
    apply Prod.ext <;> dsimp only [realNearAxisPhysical, affineRectangleEmbedding] <;> ring
  rw [physical_eq]
  exact ⟨_, affine⟩

theorem realNearAxisPhysical_injective
    (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ) :
    Function.Injective (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical) := by
  obtain ⟨bound, estimate⟩ := realNearAxisPhysical_antilipschitz
    horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical
  exact estimate.injective

theorem realNearAxisPhysical_mem_dust
    (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ)
    (horizontal_prefix : ternaryPrefix horizontal horizontalDepth = true)
    (vertical_prefix : ternaryPrefix vertical verticalDepth = true)
    (point : ℝ × ℝ) (membership : point ∈ cantorDust (1/3)) :
    realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point ∈
      cantorDust (1/3) := by
  constructor
  · exact cantor_power_scale_mem (by norm_num) (by norm_num) firstDepth
      (ternaryPrefix_cantor_embedding horizontal horizontalDepth horizontal_prefix _ membership.1)
  · apply one_sub_mem_cantorSet (by norm_num) (by norm_num)
    apply cantor_power_scale_mem (by norm_num) (by norm_num) secondDepth
    have reflected := ternaryPrefix_cantor_embedding vertical verticalDepth vertical_prefix (1-point.2)
      (one_sub_mem_cantorSet (by norm_num) (by norm_num) membership.2)
    simpa only [add_sub_assoc] using reflected

theorem realNearAxisLog_zero_drop (exponent phase : ℝ) (horizontalDepth verticalDepth : ℕ)
    (horizontal vertical scale x y : ℝ)
    (horizontal_positive : 0 < (horizontal+x)/(3 : ℝ)^horizontalDepth)
    (drop_positive : 0 < realPowerDrop exponent scale ((vertical+1-y)/(3 : ℝ)^verticalDepth))
    (zero : realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical scale x y = 0) :
    realPowerDrop exponent scale ((vertical+1-y)/(3 : ℝ)^verticalDepth) =
      (3 : ℝ)^phase*((horizontal+x)/(3 : ℝ)^horizontalDepth)^exponent := by
  apply Real.log_injOn_pos drop_positive
    (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _) (Real.rpow_pos_of_pos horizontal_positive _))
  rw [Real.log_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).ne'
    (Real.rpow_pos_of_pos horizontal_positive _).ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 3), Real.log_rpow horizontal_positive]
  unfold realNearAxisLog at zero
  linarith

theorem real_normalized_tangent_product (exponent phase : ℝ)
    (exponent_positive : 0 < exponent)
    (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ)
    (point : ℝ × ℝ)
    (u_positive : 0 < ((horizontal : ℝ)+point.1)/(3 : ℝ)^horizontalDepth)
    (y_positive : 0 < (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point).2)
    (drop_positive : 0 < realPowerDrop exponent ((1/3 : ℝ)^secondDepth)
      ((vertical+1-point.2)/(3 : ℝ)^verticalDepth))
    (zero : realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
      ((1/3 : ℝ)^secondDepth) point.1 point.2 = 0) :
    ((exponent/(horizontal+point.1))/
      realNearAxisVertical exponent vertical ((1/3 : ℝ)^secondDepth) point.2 verticalDepth)*
        realFermatTangent exponent
          (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point) =
      (3 : ℝ)^verticalDepth*(3 : ℝ)^phase/
        ((3 : ℝ)^horizontalDepth*((1/3 : ℝ)^firstDepth)^(exponent-1)) := by
  have residual := realNearAxisLog_zero_drop exponent phase horizontalDepth verticalDepth horizontal vertical
    ((1/3 : ℝ)^secondDepth) point.1 point.2 u_positive drop_positive zero
  have numerator_positive : 0 < (horizontal : ℝ)+point.1 :=
    (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < (3 : ℝ)^horizontalDepth)).mp u_positive
  have first_power_positive : 0 < ((1/3 : ℝ)^firstDepth)^(exponent-1) :=
    Real.rpow_pos_of_pos (by positivity) _
  have u_power_positive : 0 < (((horizontal : ℝ)+point.1)/(3 : ℝ)^horizontalDepth)^(exponent-1) :=
    Real.rpow_pos_of_pos u_positive _
  have y_power_positive : 0 <
      (1-(1/3 : ℝ)^secondDepth*((vertical+1-point.2)/(3 : ℝ)^verticalDepth))^(exponent-1) :=
    Real.rpow_pos_of_pos y_positive _
  have power_identity : (((horizontal : ℝ)+point.1)/(3 : ℝ)^horizontalDepth)^exponent =
      (((horizontal : ℝ)+point.1)/(3 : ℝ)^horizontalDepth)^(exponent-1)*
        (((horizontal : ℝ)+point.1)/(3 : ℝ)^horizontalDepth) := by
    conv_lhs => rw [show exponent = (exponent-1)+1 by ring]
    rw [Real.rpow_add u_positive, Real.rpow_one]
  unfold realNearAxisVertical realFermatTangent realNearAxisPhysical
  dsimp only
  rw [residual, power_identity, Real.mul_rpow (by positivity : 0 ≤ (1/3 : ℝ)^firstDepth) u_positive.le]
  -- Normalize the outer quotient without rewriting inside the real-power atoms.
  -- Their nonzeroness is supplied before the field normalization.
  conv_lhs =>
    field_simp [exponent_positive.ne', numerator_positive.ne',
      first_power_positive.ne', u_power_positive.ne', y_power_positive.ne']

theorem real_near_axis_fibre_physical (exponent phase : ℝ)
    (horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical : ℕ)
    (phase_relation : phase = (secondDepth : ℝ)-exponent*firstDepth)
    (horizontal_positive : 0 < horizontal) (vertical_positive : 0 < vertical)
    (vertical_bound : vertical+1 ≤ 3^verticalDepth)
    (small : (1/3 : ℝ)^secondDepth < 1)
    (drop_positive : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      0 < realPowerDrop exponent ((1/3 : ℝ)^secondDepth) ((vertical+1-y)/(3 : ℝ)^verticalDepth))
    (point : ℝ × ℝ) (membership : point ∈ Classical.cantorLevel
      (realNearAxisLog exponent phase horizontalDepth verticalDepth horizontal vertical
        ((1/3 : ℝ)^secondDepth)) 0) :
    0 < (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point).1 ∧
    0 < (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point).2 ∧
    (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point).1^exponent+
      (realNearAxisPhysical horizontalDepth verticalDepth firstDepth secondDepth horizontal vertical point).2^exponent=1 := by
  have first_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num) membership.1.1
  have second_bounds := cantorSet_subset_unitInterval (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num) membership.1.2
  have horizontal_real_positive : (0 : ℝ) < horizontal := by exact_mod_cast horizontal_positive
  have u_positive : 0 < ((horizontal : ℝ)+point.1)/(3 : ℝ)^horizontalDepth := by
    apply div_pos (by linarith [first_bounds.1]) (by positivity)
  have v_upper : ((vertical : ℝ)+1-point.2)/(3 : ℝ)^verticalDepth ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (3 : ℝ)^verticalDepth)).mpr
    have bound : (vertical : ℝ)+1 ≤ (3 : ℝ)^verticalDepth := by exact_mod_cast vertical_bound
    linarith [second_bounds.1]
  have y_positive : 0 < 1-(1/3 : ℝ)^secondDepth*((vertical+1-point.2)/(3 : ℝ)^verticalDepth) := by
    have multiplied := mul_le_mul_of_nonneg_left v_upper (show (0 : ℝ) ≤ (1/3 : ℝ)^secondDepth by positivity)
    nlinarith
  exact ⟨by dsimp [realNearAxisPhysical]; positivity, y_positive,
    realNearAxisLog_zero_physical_equation exponent phase horizontalDepth verticalDepth firstDepth secondDepth
      horizontal vertical point.1 point.2 phase_relation u_positive (drop_positive _ second_bounds) membership.2⟩

end LambdaCantor.RationalPowers

