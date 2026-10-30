import LambdaCantor.Circle.UniqueRoots
import LambdaCantor.Circle.RootLocation
import LambdaCantor.ParameterContinuity
import LambdaCantor.First.RootContinuity

noncomputable section
namespace LambdaCantor.Circle

def circleAddressRoot (depth : ℕ) (large : 2 ≤ depth) (digits : ℕ → Bool × Bool) : ℝ :=
  Classical.choose (circle_address_root_exists_unique depth large (fun index => (digits index).1)
    (fun index => (digits index).2))

theorem circleAddressRoot_spec (depth : ℕ) (large : 2 ≤ depth) (digits : ℕ → Bool × Bool) :
    circleAddressRoot depth large digits ∈ Set.Ioo onset (7 / 25 : ℝ) ∧
      expandedCircleResidual depth (fun ratio => address ratio (fun index => (digits index).1))
        (fun ratio => address ratio (fun index => (digits index).2)) (circleAddressRoot depth large digits) = 0 :=
  (Classical.choose_spec (circle_address_root_exists_unique depth large (fun index => (digits index).1)
    (fun index => (digits index).2))).1

theorem continuous_circleAddressRoot (depth : ℕ) (large : 2 ≤ depth) :
    Continuous (circleAddressRoot depth large) := by
  have ordered : onset ≤ (7 / 25 : ℝ) := by
    have := onset_lt_twenty_seven_hundredths
    linarith
  let rootBand : (ℕ → Bool × Bool) → Set.Icc onset (7 / 25 : ℝ) := fun digits =>
    ⟨circleAddressRoot depth large digits,
      (circleAddressRoot_spec depth large digits).1.1.le, (circleAddressRoot_spec depth large digits).1.2.le⟩
  have left_digits : Continuous (fun digits : ℕ → Bool × Bool => fun index => (digits index).1) := by
    apply continuous_pi
    intro index
    exact continuous_fst.comp (continuous_apply index)
  have right_digits : Continuous (fun digits : ℕ → Bool × Bool => fun index => (digits index).2) := by
    apply continuous_pi
    intro index
    exact continuous_snd.comp (continuous_apply index)
  have address_continuous := continuous_address_band onset_pos.le (by norm_num : (7 / 25 : ℝ) < 1) ordered
  have first_continuous : Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc onset (7 / 25 : ℝ) =>
      address point.2.val (fun index => (point.1 index).1)) :=
    address_continuous.comp (continuous_snd.prodMk (left_digits.comp continuous_fst))
  have second_continuous : Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc onset (7 / 25 : ℝ) =>
      address point.2.val (fun index => (point.1 index).2)) :=
    address_continuous.comp (continuous_snd.prodMk (right_digits.comp continuous_fst))
  have residual_continuous : Continuous (fun point : (ℕ → Bool × Bool) × Set.Icc onset (7 / 25 : ℝ) =>
      expandedCircleResidual depth (fun ratio => address ratio (fun index => (point.1 index).1))
        (fun ratio => address ratio (fun index => (point.1 index).2)) point.2.val) := by
    unfold expandedCircleResidual
    fun_prop
  have root_continuous : Continuous rootBand := continuous_unique_root _ residual_continuous rootBand
    (fun digits => (circleAddressRoot_spec depth large digits).2) (by
      intro digits parameter zero
      apply Subtype.ext
      have strict := circle_address_residual_strictAnti depth large
        (fun index => (digits index).1) (fun index => (digits index).2)
      apply strict.injOn parameter.property (rootBand digits).property
      rw [zero]
      exact (circleAddressRoot_spec depth large digits).2.symm)
  exact continuous_subtype_val.comp root_continuous

theorem isCompact_circleAddressRoot_range (depth : ℕ) (large : 2 ≤ depth) :
    IsCompact (Set.range (circleAddressRoot depth large)) :=
  isCompact_range (continuous_circleAddressRoot depth large)

end LambdaCantor.Circle
