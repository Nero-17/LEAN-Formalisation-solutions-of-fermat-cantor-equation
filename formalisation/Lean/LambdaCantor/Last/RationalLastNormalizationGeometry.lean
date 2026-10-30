import LambdaCantor.Last.AffineRectangleEmbedding
import LambdaCantor.Last.ArithmeticAlgebraicField
import LambdaCantor.Last.ReturnWords
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

noncomputable section
open scoped NNReal
namespace LambdaCantor.Last

def anisotropicPrefixMap (ratio : ℝ) (firstWord secondWord : List Bool)
    (point : ℝ × ℝ) : ℝ × ℝ :=
  (scalarWordMap ratio firstWord point.1, scalarWordMap ratio secondWord point.2)

theorem anisotropicPrefixMap_eq_affine (ratio : ℝ) (firstWord secondWord : List Bool) :
    anisotropicPrefixMap ratio firstWord secondWord =
      affineRectangleEmbedding (scalarWordMap ratio firstWord 0) (ratio^firstWord.length)
        (scalarWordMap ratio secondWord 0) (ratio^secondWord.length) := by
  funext point
  apply Prod.ext <;>
    exact scalarWordMap_affine ratio _ _

theorem continuous_anisotropicPrefixMap (ratio : ℝ) (firstWord secondWord : List Bool) :
    Continuous (anisotropicPrefixMap ratio firstWord secondWord) := by
  rw [anisotropicPrefixMap_eq_affine]
  unfold affineRectangleEmbedding
  fun_prop

theorem anisotropicPrefixMap_antilipschitz {ratio : ℝ} (positive : 0 < ratio)
    (firstWord secondWord : List Bool) :
    AntilipschitzWith
      (⟨max (ratio^firstWord.length)⁻¹ (ratio^secondWord.length)⁻¹,
        le_max_of_le_left (inv_nonneg.mpr (pow_nonneg positive.le _))⟩ : ℝ≥0)
      (anisotropicPrefixMap ratio firstWord secondWord) := by
  rw [anisotropicPrefixMap_eq_affine]
  exact affineRectangleEmbedding_antilipschitz (pow_pos positive _) (pow_pos positive _) _ _

theorem anisotropicPrefixMap_mem_dust {ratio : ℝ} (nonnegative : 0 ≤ ratio) (less_one : ratio < 1)
    (firstWord secondWord : List Bool) {point : ℝ × ℝ} (membership : point ∈ cantorDust ratio) :
    anisotropicPrefixMap ratio firstWord secondWord point ∈ cantorDust ratio :=
  ⟨scalarWordMap_mem_cantorSet nonnegative less_one firstWord membership.1,
    scalarWordMap_mem_cantorSet nonnegative less_one secondWord membership.2⟩

/-- Relative singleton openness pulls back along an actual continuous
injective map of the two actual source sets. -/
theorem isolated_point_pullback {source target : Set (ℝ × ℝ)}
    (mapping : (ℝ × ℝ) → ℝ × ℝ) (continuous_mapping : Continuous mapping)
    (injective : Function.Injective mapping) (maps : Set.MapsTo mapping source target)
    (point : target) (preimage : source) (representation : mapping preimage.val = point.val)
    (isolated : IsOpen ({point} : Set target)) : IsOpen ({preimage} : Set source) := by
  let induced : source → target := fun value => ⟨mapping value.val, maps value.property⟩
  have continuous_induced : Continuous induced :=
    (continuous_mapping.comp continuous_subtype_val).subtype_mk _
  have open_preimage := isolated.preimage continuous_induced
  have singleton_preimage : induced ⁻¹' ({point} : Set target) = ({preimage} : Set source) := by
    ext value
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro equal
      apply Subtype.ext
      apply injective
      exact (congrArg Subtype.val equal).trans representation.symm
    · intro equal
      subst value
      apply Subtype.ext
      exact representation
  rw [singleton_preimage] at open_preimage
  exact open_preimage

theorem scalarWordMap_mem_parameterField {ratio coordinate : ℝ} (word : List Bool)
    (coordinate_mem : coordinate ∈ parameterField ratio) :
    scalarWordMap ratio word coordinate ∈ parameterField ratio := by
  induction word with
  | nil => exact coordinate_mem
  | cons digit rest induction =>
    apply (parameterField ratio).add_mem
    · split_ifs
      · exact (parameterField ratio).sub_mem (parameterField ratio).one_mem (ratio_mem_parameterField ratio)
      · exact (parameterField ratio).zero_mem
    · exact (parameterField ratio).mul_mem (ratio_mem_parameterField ratio) induction

theorem anisotropicPrefixMap_coordinates_mem_parameterField {ratio : ℝ}
    (firstWord secondWord : List Bool) {point : ℝ × ℝ}
    (first_mem : point.1 ∈ parameterField ratio) (second_mem : point.2 ∈ parameterField ratio) :
    (anisotropicPrefixMap ratio firstWord secondWord point).1 ∈ parameterField ratio ∧
      (anisotropicPrefixMap ratio firstWord secondWord point).2 ∈ parameterField ratio :=
  ⟨scalarWordMap_mem_parameterField firstWord first_mem,
    scalarWordMap_mem_parameterField secondWord second_mem⟩

theorem scalarWordMap_tail_algebraic {ratio coordinate : ℝ} (positive : 0 < ratio)
    (ratio_algebraic : IsAlgebraic ℚ ratio) (word : List Bool)
    (coordinate_algebraic : IsAlgebraic ℚ (scalarWordMap ratio word coordinate)) :
    IsAlgebraic ℚ coordinate := by
  have intercept_algebraic := isAlgebraic_of_mem_parameterField ratio_algebraic
    (scalarWordMap_mem_parameterField word (parameterField ratio).zero_mem)
  have identity : coordinate =
      (scalarWordMap ratio word coordinate-scalarWordMap ratio word 0)/ratio^word.length := by
    rw [scalarWordMap_affine ratio word coordinate]
    field_simp [(pow_pos positive word.length).ne']
    <;> ring
  rw [identity, div_eq_mul_inv]
  exact (coordinate_algebraic.sub intercept_algebraic).mul ((ratio_algebraic.pow _).inv)

end LambdaCantor.Last
