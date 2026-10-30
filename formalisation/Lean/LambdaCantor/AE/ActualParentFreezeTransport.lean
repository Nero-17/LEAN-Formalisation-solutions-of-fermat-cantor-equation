import LambdaCantor.AE.PhysicalNewtonDensity
import LambdaCantor.AE.PrefixRefinementLaw
import LambdaCantor.AE.NormalizedMixtureTransport
import LambdaCantor.AE.FiniteDensityMixture
import LambdaCantor.AE.CenteredFrozenScaleBounds
import LambdaCantor.AE.FreezingPowerComparison
import LambdaCantor.AE.CenteredActualNewtonError
import LambdaCantor.AE.FreezingGeometry
import LambdaCantor.AE.NewtonTransportScale
import LambdaCantor.AE.UniformNewtonSmallness
import LambdaCantor.AE.AffineCommonSourceCoupling
import LambdaCantor.AE.ActualNewtonMixtureL1
import LambdaCantor.AE.PrefixEnergySplit
import LambdaCantor.AE.TransportFreezingIncrement
import LambdaCantor.AE.NewtonObservableConvergence
import LambdaCantor.AE.KernelLimitIdentification
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Finiteness

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology

namespace LambdaCantor.AE

private theorem real_density_unique {first second : ℝ → ℝ}
    (first_integrable : Integrable first) (second_integrable : Integrable second)
    (first_nonnegative : ∀ᵐ value : ℝ, 0 ≤ first value) (second_nonnegative : ∀ᵐ value : ℝ, 0 ≤ second value)
    (laws_equal : volume.withDensity (fun value => ENNReal.ofReal (first value)) =
      volume.withDensity (fun value => ENNReal.ofReal (second value))) : first =ᵐ[volume] second := by
  have equality := (withDensity_eq_iff_of_sigmaFinite first_integrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    second_integrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp laws_equal
  filter_upwards [equality, first_nonnegative, second_nonnegative] with value equality first_positive second_positive
  have real_equality := congrArg ENNReal.toReal equality
  simpa only [ENNReal.toReal_ofReal first_positive, ENNReal.toReal_ofReal second_positive] using real_equality

private theorem weighted_snoc_real (depth : ℕ) (function : (Fin (depth+1) → Bool × Bool) → ℝ) :
    (∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*
      ∑ digit : Bool × Bool, (1/4 : ℝ)*function (Fin.snoc word digit)) =
        ∑ child : Fin (depth+1) → Bool × Bool, (1/4 : ℝ)^(depth+1)*function child := by
  calc
    _ = ∑ word : Fin depth → Bool × Bool, ∑ digit : Bool × Bool,
        (1/4 : ℝ)^(depth+1)*function (Fin.snoc word digit) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro digit _
      rw [pow_succ]
      ring
    _ = ∑ digit : Bool × Bool, ∑ word : Fin depth → Bool × Bool,
        (1/4 : ℝ)^(depth+1)*function (Fin.snoc word digit) := Finset.sum_comm
    _ = _ := (paired_word_snoc_sum depth
      (fun child : Fin (depth+1) → Bool × Bool =>
        (1/4 : ℝ)^(depth+1)*function child)).symm

private theorem weighted_snoc_measure (depth : ℕ) (function : (Fin (depth+1) → Bool × Bool) → Measure ℝ) :
    (∑ word : Fin depth → Bool × Bool, ((4 : ℝ≥0∞)⁻¹^depth) •
      ∑ digit : Bool × Bool, (4 : ℝ≥0∞)⁻¹ • function (Fin.snoc word digit)) =
        ∑ child : Fin (depth+1) → Bool × Bool, ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function child := by
  calc
    _ = ∑ word : Fin depth → Bool × Bool, ∑ digit : Bool × Bool,
        ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function (Fin.snoc word digit) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro digit _
      rw [smul_smul, pow_succ]
    _ = ∑ digit : Bool × Bool, ∑ word : Fin depth → Bool × Bool,
        ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function (Fin.snoc word digit) := Finset.sum_comm
    _ = _ := by
      have reindex :
          (∑ pair : (Bool × Bool) × (Fin depth → Bool × Bool),
            ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function (Fin.snoc pair.2 pair.1)) =
              ∑ child : Fin (depth+1) → Bool × Bool,
                ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function child :=
        (Fin.snocEquiv (fun _ : Fin (depth+1) => Bool × Bool)).sum_comp
          (fun child : Fin (depth+1) → Bool × Bool =>
            ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function child)
      have product_sum :
          (∑ pair : (Bool × Bool) × (Fin depth → Bool × Bool),
            ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function (Fin.snoc pair.2 pair.1)) =
              ∑ digit : Bool × Bool, ∑ word : Fin depth → Bool × Bool,
                ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function (Fin.snoc word digit) :=
        Fintype.sum_prod_type (fun pair : (Bool × Bool) × (Fin depth → Bool × Bool) =>
          ((4 : ℝ≥0∞)⁻¹^(depth+1)) • function (Fin.snoc pair.2 pair.1))
      exact product_sum.symm.trans reindex

private theorem actual_depth_L1_increment_of_parent_replacements
    (kernels : ∀ depth, (Fin depth → Bool × Bool) → FrozenNewtonKernel)
    (first second : ∀ depth, (Fin depth → Bool × Bool) → ℝ → ℝ)
    (majorant : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
    (first_integrable : ∀ depth word, Integrable (first depth word))
    (second_integrable : ∀ depth word, Integrable (second depth word))
    (first_nonnegative : ∀ depth word, ∀ᵐ value : ℝ, 0 ≤ first depth word value)
    (second_nonnegative : ∀ depth word, ∀ᵐ value : ℝ, 0 ≤ second depth word value)
    (first_law : ∀ depth word, (kernels depth word).law =
      volume.withDensity (fun value => ENNReal.ofReal (first depth word value)))
    (second_law : ∀ depth word,
      (∑ digit : Bool × Bool, (4 : ℝ≥0∞)⁻¹ • (kernels (depth+1) (Fin.snoc word digit)).law) =
        volume.withDensity (fun value => ENNReal.ofReal (second depth word value)))
    (replacements : ∀ depth word, (∫ value : ℝ, |first depth word value-second depth word value|) ≤ majorant depth word) :
    ∃ densities : ℕ → Lp ℝ 1 volume,
      (∀ depth, 0 ≤ densities depth) ∧
      (∀ depth, First.Roots.pairedAddressMeasure.map (newtonMixtureObservable depth (kernels depth)) =
        volume.withDensity (fun value => ENNReal.ofReal (densities depth value))) ∧
      ∀ depth, ‖densities (depth+1)-densities depth‖ ≤
        ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*majorant depth word := by
  classical
  have exists_density := fun depth => actual_newton_mixture_L1 depth (kernels depth) (first depth)
    (first_integrable depth) (first_nonnegative depth) (first_law depth)
  choose densities density_nonnegative representatives density_laws using exists_density
  refine ⟨densities, density_nonnegative, density_laws, ?_⟩
  intro depth
  let firstMixture := fun value => ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*first depth word value
  let secondMixture := fun value => ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*second depth word value
  have firstMixture_integrable : Integrable firstMixture :=
    integrable_finset_sum _ (fun word _ => (first_integrable depth word).const_mul _)
  have secondMixture_integrable : Integrable secondMixture :=
    integrable_finset_sum _ (fun word _ => (second_integrable depth word).const_mul _)
  have secondMixture_nonnegative : ∀ᵐ value : ℝ, 0 ≤ secondMixture value := by
    have all_nonnegative := ae_all_iff.mpr (second_nonnegative depth)
    filter_upwards [all_nonnegative] with value nonnegative
    exact Finset.sum_nonneg (fun word _ => mul_nonneg (by positivity) (nonnegative word))
  have weight : ENNReal.ofReal ((1/4 : ℝ)^depth) = (4 : ℝ≥0∞)⁻¹^depth := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/4)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have secondMixture_law : First.Roots.pairedAddressMeasure.map
      (newtonMixtureObservable (depth+1) (kernels (depth+1))) =
        volume.withDensity (fun value => ENNReal.ofReal (secondMixture value)) := by
    rw [newtonMixtureObservable_law, ← weighted_snoc_measure depth (fun word => (kernels (depth+1) word).law)]
    simp_rw [second_law depth]
    have law := withDensity_finite_real_mixture (fun _word : Fin depth → Bool × Bool => (1/4 : ℝ)^depth)
      (second depth) (fun _ => by positivity) (fun word => (second_integrable depth word).aestronglyMeasurable)
      (second_nonnegative depth)
    simpa only [weight, secondMixture] using law.symm
  have next_representative : (densities (depth+1) : ℝ → ℝ) =ᵐ[volume] secondMixture :=
    real_density_unique (L1.integrable_coeFn (densities (depth+1))) secondMixture_integrable
      ((Lp.coeFn_nonneg _).mpr (density_nonnegative (depth+1))) secondMixture_nonnegative
      ((density_laws (depth+1)).symm.trans secondMixture_law)
  have norm_identity : ‖densities (depth+1)-densities depth‖ =
      ∫ value : ℝ, |firstMixture value-secondMixture value| := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (densities (depth+1)) (densities depth), next_representative, representatives depth]
      with value subtraction next current
    rw [subtraction, Pi.sub_apply, next, current, Real.norm_eq_abs, abs_sub_comm]
  rw [norm_identity]
  apply (finite_mixture_L1_distance_le Finset.univ (fun _word : Fin depth → Bool × Bool => (1/4 : ℝ)^depth)
    (first depth) (second depth) (fun _ _ => by positivity)
    (fun word _ => first_integrable depth word) (fun word _ => second_integrable depth word)).trans
  exact Finset.sum_le_sum (fun word _ => mul_le_mul_of_nonneg_left (replacements depth word) (by positivity))

private theorem averaged_parent_energy_bound
    (energy : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
    (energy_nonnegative : ∀ depth word, 0 ≤ energy depth word)
    {coefficient averageConstant upper dimension : ℝ}
    (coefficient_nonnegative : 0 ≤ coefficient) (upper_positive : 0 < upper)
    (average : ∀ depth, (∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*(1+energy depth word)) ≤
      averageConstant*upper^(-(depth : ℝ)*(1-dimension))) (depth : ℕ) :
    (∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*
      ∑ digit : Bool × Bool, (1/4 : ℝ)*(1+coefficient*(1+energy depth word+energy (depth+1) (Fin.snoc word digit)))) ≤
      ((1+coefficient)*averageConstant*(1+upper^(-(1-dimension))))*upper^(-(depth : ℝ)*(1-dimension)) := by
  classical
  have quarter_sum : (∑ _digit : Bool × Bool, (1/4 : ℝ)) = 1 := by norm_num [Fintype.sum_prod_type]
  have component_bound : ∀ word : Fin depth → Bool × Bool,
      (∑ digit : Bool × Bool, (1/4 : ℝ)*(1+coefficient*(1+energy depth word+energy (depth+1) (Fin.snoc word digit)))) ≤
        (1+coefficient)*((1+energy depth word)+∑ digit : Bool × Bool, (1/4 : ℝ)*(1+energy (depth+1) (Fin.snoc word digit))) := by
    intro word
    calc
      _ ≤ ∑ digit : Bool × Bool, (1/4 : ℝ)*
          ((1+coefficient)*((1+energy depth word)+(1+energy (depth+1) (Fin.snoc word digit)))) := by
        apply Finset.sum_le_sum
        intro digit _
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        nlinarith [energy_nonnegative depth word, energy_nonnegative (depth+1) (Fin.snoc word digit)]
      _ = _ := by
        have identity : ∀ digit : Bool × Bool, (1/4 : ℝ)*
            ((1+coefficient)*((1+energy depth word)+(1+energy (depth+1) (Fin.snoc word digit)))) =
            ((1+coefficient)*(1+energy depth word))*(1/4 : ℝ)+
              (1+coefficient)*((1/4 : ℝ)*(1+energy (depth+1) (Fin.snoc word digit))) := by
          intro digit
          ring
        simp_rw [identity]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, quarter_sum, mul_one]
        ring
  have next_power : upper^(-(((depth+1 : ℕ) : ℝ))*(1-dimension)) =
      upper^(-(1-dimension))*upper^(-(depth : ℝ)*(1-dimension)) := by
    rw [← Real.rpow_add upper_positive]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*
        ((1+coefficient)*((1+energy depth word)+∑ digit : Bool × Bool, (1/4 : ℝ)*(1+energy (depth+1) (Fin.snoc word digit)))) :=
      Finset.sum_le_sum (fun word _ => mul_le_mul_of_nonneg_left (component_bound word) (by positivity))
    _ = (1+coefficient)*((∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*(1+energy depth word))+
        ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*
          ∑ digit : Bool × Bool, (1/4 : ℝ)*(1+energy (depth+1) (Fin.snoc word digit))) := by
      conv_rhs => rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro word _
      ring
    _ = (1+coefficient)*((∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*(1+energy depth word))+
        ∑ child : Fin (depth+1) → Bool × Bool, (1/4 : ℝ)^(depth+1)*(1+energy (depth+1) child)) := by
      rw [weighted_snoc_real depth (fun child : Fin (depth+1) → Bool × Bool => 1+energy (depth+1) child)]
    _ ≤ (1+coefficient)*(averageConstant*upper^(-(depth : ℝ)*(1-dimension))+
        averageConstant*upper^(-(((depth+1 : ℕ) : ℝ))*(1-dimension))) :=
      mul_le_mul_of_nonneg_left (add_le_add (average depth) (average (depth+1))) (by linarith)
    _ = _ := by rw [next_power]; ring

private theorem averaged_parent_geometric_increment
    (energy : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
    (energy_nonnegative : ∀ depth word, 0 ≤ energy depth word)
    {coefficient averageConstant constant costConstant lower upper regularity rho : ℝ}
    (coefficient_nonnegative : 0 ≤ coefficient) (average_nonnegative : 0 ≤ averageConstant)
    (constant_nonnegative : 0 ≤ constant) (costConstant_nonnegative : 0 ≤ costConstant)
    (lower_positive : 0 < lower) (upper_positive : 0 < upper) (regularity_positive : 0 < regularity)
    (rho_nonnegative : 0 ≤ rho)
    (average : ∀ depth, (∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*(1+energy depth word)) ≤
      averageConstant*upper^(-(depth : ℝ)*(1-Real.log 2/Real.log (1/lower)))) (shift depth : ℕ) :
    (∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*
      (constant*(∑ digit : Bool × Bool, (1/4 : ℝ)*(1+coefficient*(1+energy depth word+energy (depth+1) (Fin.snoc word digit))))^
        (1/(2*(1+regularity)))*(costConstant*rho*(((shift+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth)^(regularity/(1+regularity)))) ≤
      (constant*((1+coefficient)*averageConstant*(1+upper^(-(1-Real.log 2/Real.log (1/lower)))))^(1/(2*(1+regularity)))*
        costConstant^(regularity/(1+regularity)))*rho^(regularity/(1+regularity))*
          (((shift+depth+1 : ℕ) : ℝ))*freezingRatio lower upper regularity^depth := by
  classical
  let amplitudeSquared := fun word : Fin depth → Bool × Bool =>
    ∑ digit : Bool × Bool, (1/4 : ℝ)*(1+coefficient*(1+energy depth word+energy (depth+1) (Fin.snoc word digit)))
  have amplitude_nonnegative : ∀ word, 0 ≤ amplitudeSquared word := by
    intro word
    exact Finset.sum_nonneg (fun digit _ => by
      have parent_nonnegative := energy_nonnegative depth word
      have child_nonnegative := energy_nonnegative (depth+1) (Fin.snoc word digit)
      positivity)
  have exponent_nonnegative : 0 ≤ 1/(2*(1+regularity)) := by positivity
  have exponent_le_one : 1/(2*(1+regularity)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2*(1+regularity))).mpr
    linarith
  have jensen := (Real.concaveOn_rpow exponent_nonnegative exponent_le_one).le_map_sum
    (fun word (_ : word ∈ (Finset.univ : Finset (Fin depth → Bool × Bool))) =>
      show (0 : ℝ) ≤ (1/4 : ℝ)^depth by positivity)
    (paired_prefix_weights_sum depth) (fun word _ => amplitude_nonnegative word)
  simp only [smul_eq_mul] at jensen
  have energy_nonnegative' : 0 ≤ ∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*amplitudeSquared word :=
    Finset.sum_nonneg (fun word _ => mul_nonneg (by positivity) (amplitude_nonnegative word))
  have energy_bound := averaged_parent_energy_bound energy energy_nonnegative coefficient_nonnegative upper_positive average depth
  have cost_nonnegative : 0 ≤ costConstant*rho*(((shift+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth := by positivity
  have scalar := transport_freezing_increment_bound shift depth lower_positive upper_positive regularity_positive
    constant_nonnegative (by positivity) costConstant_nonnegative rho_nonnegative energy_nonnegative' cost_nonnegative
    energy_bound (le_refl (costConstant*rho*(((shift+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth))
  calc
    _ = constant*(∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*amplitudeSquared word^(1/(2*(1+regularity))))*
        (costConstant*rho*(((shift+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth)^(regularity/(1+regularity)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro word _
      dsimp [amplitudeSquared]
      ring
    _ ≤ constant*(∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*amplitudeSquared word)^(1/(2*(1+regularity)))*
        (costConstant*rho*(((shift+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth)^(regularity/(1+regularity)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left jensen constant_nonnegative) (by positivity)
    _ ≤ _ := scalar

private def prefixFreshTail {depth : ℕ} (word : Fin depth → Bool × Bool)
    (tail : ℕ → Bool × Bool) (index : ℕ) : Bool × Bool :=
  if before : index < depth then word ⟨index, before⟩ else tail (index-depth)

private theorem prefixFreshTail_word {depth : ℕ} (word : Fin depth → Bool × Bool)
    (tail : ℕ → Bool × Bool) : (fun index : Fin depth => prefixFreshTail word tail index) = word := by
  funext index
  simp only [prefixFreshTail, dif_pos index.isLt]

private theorem prefixFreshTail_tail {depth : ℕ} (word : Fin depth → Bool × Bool)
    (tail : ℕ → Bool × Bool) : (fun index => prefixFreshTail word tail (index+depth)) = tail := by
  funext index
  simp only [prefixFreshTail, dif_neg (show ¬index+depth < depth by omega), Nat.add_sub_cancel_right]

private theorem prefixFreshTail_snoc {depth : ℕ} (word : Fin depth → Bool × Bool)
    (digit : Bool × Bool) (tail : ℕ → Bool × Bool) :
    prefixFreshTail (Fin.snoc word digit) tail = prefixFreshTail word (prependNewtonDigit digit tail) := by
  funext index
  by_cases before : index < depth
  · have before_child : index < depth+1 := by omega
    simp only [prefixFreshTail, dif_pos before, dif_pos before_child, Fin.snoc]
    rfl
  · by_cases last : index = depth
    · subst index
      simp [prefixFreshTail, Fin.snoc, prependNewtonDigit]
    · have before_child : ¬index < depth+1 := by omega
      have tail_nonzero : index-depth ≠ 0 := by omega
      simp only [prefixFreshTail, dif_neg before, dif_neg before_child,
        prependNewtonDigit, if_neg tail_nonzero]
      congr 1

private theorem actual_prefix_newton_estimate
    {exponent freezing upper rho normalizedBound mixedBound secondBound displacementConstant slope : ℝ}
    (exponent_greater_one : 1 < exponent)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (word : Fin depth → Bool × Bool)
    (root : (ℕ → Bool × Bool) → ℝ)
    (rho_nonnegative : 0 ≤ rho) (normalized_nonnegative : 0 ≤ normalizedBound)
    (mixed_nonnegative : 0 ≤ mixedBound) (second_nonnegative : 0 ≤ secondBound)
    (displacement_nonnegative : 0 ≤ displacementConstant) (slope_positive : 0 < slope)
    (vertical_large : 1 ≤ verticalDepth)
    (band : ∀ tail parameter, parameter ∈ uIcc freezing (root (prefixFreshTail word tail)) →
      0 < parameter ∧ parameter < 1 ∧ parameter^tailDepth ≤ 1/2 ∧ parameter^verticalDepth ≤ 1/2)
    (freezing_upper : freezing ≤ upper) (tail_rho : freezing^tailDepth ≤ 2*rho)
    (normalized_bound : (verticalDepth : ℝ)^2*
      (freezing^(-exponent*(horizontalDepth : ℝ))*(freezing^verticalDepth)^2) ≤ normalizedBound)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (derivative_negative : deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) freezing ≤ -slope)
    (second_bound : ∀ tail parameter, parameter ∈ uIcc freezing (root (prefixFreshTail word tail)) →
      |centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth
        (pairedZeroPrefixDigits depth (prefixFreshTail word tail)) parameter| ≤ secondBound)
    (mixed_bound : ∀ tail parameter, parameter ∈ uIcc freezing (root (prefixFreshTail word tail)) →
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth (prefixFreshTail word tail)) parameter-
        deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth
          (pairedZeroPrefixDigits depth (prefixFreshTail word tail))) parameter| ≤
          mixedBound*rho*(((tailDepth+depth+1 : ℕ) : ℝ))*upper^depth)
    (root_displacement : ∀ tail, |root (prefixFreshTail word tail)-freezing| ≤ displacementConstant*rho*upper^depth) :
    ∀ tail, |root (prefixFreshTail word tail)-
      (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word freezing).value tail| ≤
      ((4*(exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*(1+normalizedBound)+
        mixedBound*displacementConstant+secondBound*displacementConstant^2)/slope)*
          rho^2*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^depth)^2 := by
  intro tail
  have slope_lower : slope ≤ |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) freezing| := by
    linarith [neg_le_abs (deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) freezing)]
  have estimate := centered_actual_newton_quadratic_error exponent_greater_one horizontalDepth verticalDepth tailDepth depth
    (prefixFreshTail word tail) rho_nonnegative normalized_nonnegative mixed_nonnegative second_nonnegative
    displacement_nonnegative slope_positive vertical_large (band tail) freezing_upper tail_rho normalized_bound
    (root_zero _) (by simpa only [prefixFreshTail_word] using slope_lower) (second_bound tail) (mixed_bound tail)
    (root_displacement tail)
  simpa only [prefixFreshTail_word, prefixFreshTail_tail] using estimate

def actualParentUniformMinimum (exponent lower discrepancyBound derivativeBound : ℝ) : ℝ :=
  lower*min (exponent*(1/2 : ℝ)^(exponent-1)/(2*derivativeBound))
    (exponent*lower^discrepancyBound*(1/2 : ℝ)^(exponent-1)/(2*derivativeBound))/2

def actualParentUniformRadius (exponent lower discrepancyBound slope : ℝ) : ℝ :=
  3*(2*exponent*(1+lower^(-discrepancyBound))/slope)+1

def actualParentNewtonErrorConstant (exponent normalizedBound mixedBound secondBound displacementConstant slope : ℝ) : ℝ :=
  (4*(exponent*(exponent-1)*max 1 ((1/2 : ℝ)^(exponent-2)))*(1+normalizedBound)+
    mixedBound*(2*displacementConstant)+secondBound*(2*displacementConstant)^2)/slope

private theorem kernel_value_zero (kernel : FrozenNewtonKernel) :
    kernel.value (fun _ => (false, false)) = kernel.affineCenter := by
  rw [kernel.value_eq_affine]
  simp [address]

theorem actualParentUniformMinimum_positive {exponent lower discrepancyBound derivativeBound : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower) (derivative_positive : 0 < derivativeBound) :
    0 < actualParentUniformMinimum exponent lower discrepancyBound derivativeBound := by
  have exponent_positive : 0 < exponent := by linarith
  unfold actualParentUniformMinimum
  positivity

theorem actualParentUniformRadius_positive {exponent lower discrepancyBound slope : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower) (slope_positive : 0 < slope) :
    0 < actualParentUniformRadius exponent lower discrepancyBound slope := by
  have exponent_positive : 0 < exponent := by linarith
  unfold actualParentUniformRadius
  positivity

private theorem centered_frozen_positive_scales {exponent ratio : ℝ}
    (exponent_greater_one : 1 < exponent) (positive : 0 < ratio) (less_one : ratio < 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (word : Fin depth → Bool × Bool)
    (tail_small : ratio^tailDepth ≤ 1/2) (vertical_small : ratio^verticalDepth ≤ 1/2)
    (derivative_negative : deriv
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) ratio < 0) :
    0 < (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word ratio).firstScale ∧
      0 < (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word ratio).secondScale := by
  have exponent_positive : 0 < exponent := by linarith
  have first_base : 0 < 1-ratio^tailDepth+ratio^tailDepth*
      address ratio (fun index => if before : index < depth then (word ⟨index, before⟩).1 else false) := by
    have nonnegative := address_nonnegative positive.le less_one
      (fun index => if before : index < depth then (word ⟨index, before⟩).1 else false)
    have product := mul_nonneg (pow_nonneg positive.le tailDepth) nonnegative
    linarith
  have second_base : 0 < 1-ratio^verticalDepth+ratio^(verticalDepth+tailDepth)*
      address ratio (fun index => if before : index < depth then (word ⟨index, before⟩).2 else false) := by
    have nonnegative := address_nonnegative positive.le less_one
      (fun index => if before : index < depth then (word ⟨index, before⟩).2 else false)
    have product := mul_nonneg (pow_nonneg positive.le (verticalDepth+tailDepth)) nonnegative
    linarith
  have first := centeredNewtonFirstCoefficient_positive tailDepth depth exponent_positive positive first_base
  have second := centeredNewtonSecondCoefficient_positive horizontalDepth verticalDepth tailDepth depth
    exponent_positive positive second_base
  exact ⟨div_pos_of_neg_of_neg (neg_neg_of_pos first) derivative_negative,
    div_pos_of_neg_of_neg (neg_neg_of_pos second) derivative_negative⟩

private theorem child_firstScale (kernel : FrozenNewtonKernel) (digit : Bool × Bool) :
    (kernel.child digit).firstScale = kernel.firstScale*kernel.freezing := by
  unfold FrozenNewtonKernel.child FrozenNewtonKernel.firstScale
  ring

private theorem child_secondScale (kernel : FrozenNewtonKernel) (digit : Bool × Bool) :
    (kernel.child digit).secondScale = kernel.secondScale*kernel.freezing := by
  unfold FrozenNewtonKernel.child FrozenNewtonKernel.secondScale
  ring

private theorem finite_energy_amplitude_bound
    {coefficient parentEnergy childEnergy : ℝ≥0∞}
    (coefficient_finite : coefficient ≠ ⊤) (parent_finite : parentEnergy ≠ ⊤) (child_finite : childEnergy ≠ ⊤) :
    coefficient*parentEnergy ≤ ENNReal.ofReal
      ((Real.sqrt (1+coefficient.toReal*(1+parentEnergy.toReal+childEnergy.toReal)))^2) ∧
    coefficient*childEnergy ≤ ENNReal.ofReal
      ((Real.sqrt (1+coefficient.toReal*(1+parentEnergy.toReal+childEnergy.toReal)))^2) := by
  have square : (Real.sqrt (1+coefficient.toReal*(1+parentEnergy.toReal+childEnergy.toReal)))^2 =
      1+coefficient.toReal*(1+parentEnergy.toReal+childEnergy.toReal) := Real.sq_sqrt (by positivity)
  have parent_le : parentEnergy ≤ ENNReal.ofReal (1+parentEnergy.toReal+childEnergy.toReal) := by
    calc
      parentEnergy = ENNReal.ofReal parentEnergy.toReal :=
        (ENNReal.ofReal_toReal parent_finite).symm
      _ ≤ ENNReal.ofReal (1+parentEnergy.toReal+childEnergy.toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := childEnergy)])
  have child_le : childEnergy ≤ ENNReal.ofReal (1+parentEnergy.toReal+childEnergy.toReal) := by
    calc
      childEnergy = ENNReal.ofReal childEnergy.toReal :=
        (ENNReal.ofReal_toReal child_finite).symm
      _ ≤ ENNReal.ofReal (1+parentEnergy.toReal+childEnergy.toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith [ENNReal.toReal_nonneg (a := parentEnergy)])
  have common : coefficient*ENNReal.ofReal (1+parentEnergy.toReal+childEnergy.toReal) ≤
      ENNReal.ofReal ((Real.sqrt (1+coefficient.toReal*(1+parentEnergy.toReal+childEnergy.toReal)))^2) := by
    calc
      _ = ENNReal.ofReal (coefficient.toReal*(1+parentEnergy.toReal+childEnergy.toReal)) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal coefficient_finite]
      _ ≤ _ := by rw [square]; exact ENNReal.ofReal_le_ofReal (by linarith)
  exact ⟨(mul_le_mul_left' parent_le coefficient).trans common,
    (mul_le_mul_left' child_le coefficient).trans common⟩

/-- A fixed transport constant depending only on the common normalized support radius. -/
def actualParentFreezeTransportConstant (radius : ℝ) (nonnegative : 0 ≤ radius) : ℝ :=
  Classical.choose (exists_normalized_finite_mixture_transport_constant (Index := Bool × Bool) nonnegative)
/-- Concrete replacement of one actual parent by its four newly frozen
centered children. All density, support, coupling, and transport hypotheses
are constructed from the displayed finite-energy freezing data. The
constants here are local to this parent; uniform depth bounds remain a
separate application of the centered width and Newton-error estimates. -/
theorem actual_parent_frozen_mixture_transport
    {exponent parentFreezing rho regularity : ℝ}
    (exponent_greater_one : 1 < exponent) (rho_positive : 0 < rho)
    (regularity_positive : 0 < regularity) (regularity_le_one : regularity ≤ 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (word : Fin depth → Bool × Bool)
    (childFreezing : Bool × Bool → ℝ)
    (parent_positive : 0 < parentFreezing) (parent_less_one : parentFreezing < 1)
    (children_positive : ∀ digit, 0 < childFreezing digit)
    (children_less_one : ∀ digit, childFreezing digit < 1)
    (parent_tail_small : parentFreezing^tailDepth ≤ 1/2)
    (parent_vertical_small : parentFreezing^verticalDepth ≤ 1/2)
    (children_tail_small : ∀ digit, childFreezing digit^tailDepth ≤ 1/2)
    (children_vertical_small : ∀ digit, childFreezing digit^verticalDepth ≤ 1/2)
    (parent_derivative_negative : deriv
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) parentFreezing < 0)
    (children_derivative_negative : ∀ digit, deriv
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth (depth+1) (Fin.snoc word digit))
        (childFreezing digit) < 0)
    (parent_energy_finite : fullFourierEnergy parentFreezing regularity < ⊤)
    (children_energy_finite : ∀ digit, fullFourierEnergy (childFreezing digit) regularity < ⊤) :
    let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
    let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit) (childFreezing digit)
    let width := rho*parentFreezing^depth
    let origins := fun digit => (parent.child digit).affineCenter
    let couplings := fun digit => commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail => ((parent.child digit).value tail-origins digit)/width)
      (fun tail => ((children digit).value tail-origins digit)/width)
    ∃ minimum radius constant : ℝ, 0 < minimum ∧ 0 < radius ∧ 0 < constant ∧
      ∃ first second : (Bool × Bool) → ℝ → ℝ,
      parent.law = volume.withDensity (fun value => ENNReal.ofReal
        (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)) ∧
      (∑ digit : Bool × Bool, (4 : ℝ≥0∞)⁻¹ • (children digit).law) =
        volume.withDensity (fun value => ENNReal.ofReal
          (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value)) ∧
      (∀ digit, Integrable (first digit) ∧ Integrable (second digit) ∧
        (∀ value, 0 ≤ first digit value) ∧ (∀ value, 0 ≤ second digit value) ∧
        Function.support (first digit) ⊆ Icc (-radius) radius ∧
        Function.support (second digit) ⊆ Icc (-radius) radius) ∧
      (∀ digit, Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (couplings digit)) ∧
      (∫ value : ℝ, |(∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)-
        ∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value|) ≤
        constant*(∑ digit : Bool × Bool, (1/4 : ℝ)*
          (1+(2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)).toReal*
            (1+(fullFourierEnergy parentFreezing regularity).toReal+
              (fullFourierEnergy (childFreezing digit) regularity).toReal)))^(1/(2*(1+regularity)))*
          (∑ digit : Bool × Bool, ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings digit)^(regularity/(1+regularity)) := by
  classical
  dsimp only
  let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
  let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
    (depth+1) (Fin.snoc word digit) (childFreezing digit)
  let old := fun digit => parent.child digit
  let width := rho*parentFreezing^depth
  let origins := fun digit => (old digit).affineCenter
  have width_positive : 0 < width := by dsimp [width]; positivity
  have parent_scales := centered_frozen_positive_scales exponent_greater_one parent_positive parent_less_one
    horizontalDepth verticalDepth tailDepth depth word parent_tail_small parent_vertical_small parent_derivative_negative
  have old_scales : ∀ digit, 0 < (old digit).firstScale ∧ 0 < (old digit).secondScale := by
    intro digit
    dsimp [old]
    rw [child_firstScale, child_secondScale]
    exact ⟨mul_pos parent_scales.1 parent_positive, mul_pos parent_scales.2 parent_positive⟩
  have child_scales : ∀ digit, 0 < (children digit).firstScale ∧ 0 < (children digit).secondScale := by
    intro digit
    exact centered_frozen_positive_scales exponent_greater_one (children_positive digit) (children_less_one digit)
      horizontalDepth verticalDepth tailDepth (depth+1) (Fin.snoc word digit)
      (children_tail_small digit) (children_vertical_small digit) (children_derivative_negative digit)
  let componentMinimum := fun digit => min ((old digit).firstScale/width)
    (min ((old digit).secondScale/width) (min ((children digit).firstScale/width) ((children digit).secondScale/width)))
  obtain ⟨minimumDigit, _, minimum_le⟩ := Finset.exists_min_image Finset.univ componentMinimum (by simp)
  let minimum := componentMinimum minimumDigit
  have minimum_positive : 0 < minimum := by
    dsimp [minimum, componentMinimum]
    exact lt_min (div_pos (old_scales _).1 width_positive)
      (lt_min (div_pos (old_scales _).2 width_positive)
        (lt_min (div_pos (child_scales _).1 width_positive) (div_pos (child_scales _).2 width_positive)))
  have coefficient_lower : ∀ digit,
      minimum ≤ (old digit).firstScale/width ∧ minimum ≤ (old digit).secondScale/width ∧
      minimum ≤ (children digit).firstScale/width ∧ minimum ≤ (children digit).secondScale/width := by
    intro digit
    have bound := minimum_le digit (Finset.mem_univ digit)
    exact ⟨bound.trans (min_le_left _ _),
      bound.trans ((min_le_right _ _).trans (min_le_left _ _)),
      bound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
      bound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  let supportTerm := fun digit => ((old digit).firstScale+(old digit).secondScale+
    |(children digit).affineCenter-origins digit|+(children digit).firstScale+(children digit).secondScale)/width
  have term_nonnegative : ∀ digit, 0 ≤ supportTerm digit := by
    intro digit
    dsimp [supportTerm]
    exact div_nonneg (by linarith [(old_scales digit).1, (old_scales digit).2,
      (child_scales digit).1, (child_scales digit).2, abs_nonneg ((children digit).affineCenter-origins digit)]) width_positive.le
  let radius := 1+∑ digit : Bool × Bool, supportTerm digit
  have radius_positive : 0 < radius := by
    have sum_nonnegative : 0 ≤ ∑ digit : Bool × Bool, supportTerm digit :=
      Finset.sum_nonneg (fun digit _ => term_nonnegative digit)
    dsimp [radius]
    linarith
  have term_radius : ∀ digit, supportTerm digit ≤ radius := by
    intro digit
    have bound := Finset.single_le_sum (fun other _ => term_nonnegative other) (Finset.mem_univ digit)
    dsimp [radius]
    linarith
  have old_support : ∀ digit tail, |((old digit).value tail-origins digit)/width| ≤ radius := by
    intro digit tail
    rw [abs_div, abs_of_pos width_positive]
    apply (div_le_div_of_nonneg_right ((old digit).value_affine_support parent_positive.le parent_less_one
      (old_scales digit).1.le (old_scales digit).2.le tail) width_positive.le).trans
    apply (div_le_div_of_nonneg_right (show (old digit).firstScale+(old digit).secondScale ≤
      (old digit).firstScale+(old digit).secondScale+|(children digit).affineCenter-origins digit|+
        (children digit).firstScale+(children digit).secondScale by
      linarith [(child_scales digit).1, (child_scales digit).2,
        abs_nonneg ((children digit).affineCenter-origins digit)]) width_positive.le).trans
    exact term_radius digit
  have new_support : ∀ digit tail, |((children digit).value tail-origins digit)/width| ≤ radius := by
    intro digit tail
    have triangle := (abs_sub_le ((children digit).value tail) ((children digit).affineCenter) (origins digit)).trans
      (add_le_add ((children digit).value_affine_support (children_positive digit).le (children_less_one digit)
        (child_scales digit).1.le (child_scales digit).2.le tail)
        (le_refl |(children digit).affineCenter-origins digit|))
    rw [abs_div, abs_of_pos width_positive]
    apply (div_le_div_of_nonneg_right triangle width_positive.le).trans
    apply (div_le_div_of_nonneg_right (show (children digit).firstScale+(children digit).secondScale+
      |(children digit).affineCenter-origins digit| ≤
      (old digit).firstScale+(old digit).secondScale+|(children digit).affineCenter-origins digit|+
        (children digit).firstScale+(children digit).secondScale by
      linarith [(old_scales digit).1, (old_scales digit).2]) width_positive.le).trans
    exact term_radius digit
  have first_exists := fun digit => actual_normalized_newton_density (old digit) width_positive minimum_positive
    (coefficient_lower digit).1 (coefficient_lower digit).2.1 regularity_positive.le
    parent_energy_finite (old_support digit)
  have second_exists := fun digit => actual_normalized_newton_density (children digit) width_positive minimum_positive
    (coefficient_lower digit).2.2.1 (coefficient_lower digit).2.2.2 regularity_positive.le
    (children_energy_finite digit) (new_support digit)
  choose first first_integrable first_square first_nonnegative first_support first_law first_physical first_weighted using first_exists
  choose second second_integrable second_square second_nonnegative second_support second_law second_physical second_weighted using second_exists
  let coefficient : ℝ≥0∞ := 2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)
  have coefficient_finite : coefficient ≠ ⊤ := by dsimp [coefficient]; finiteness
  let amplitude := fun digit => Real.sqrt (1+coefficient.toReal*
    (1+(fullFourierEnergy parentFreezing regularity).toReal+(fullFourierEnergy (childFreezing digit) regularity).toReal))
  have amplitude_lower : ∀ digit, 1 ≤ amplitude digit := by
    intro digit
    dsimp [amplitude]
    apply Real.one_le_sqrt.mpr
    have product_nonnegative : 0 ≤ coefficient.toReal*
        (1+(fullFourierEnergy parentFreezing regularity).toReal+(fullFourierEnergy (childFreezing digit) regularity).toReal) := by positivity
    linarith
  have amplitude_square : ∀ digit, amplitude digit^2 = 1+coefficient.toReal*
      (1+(fullFourierEnergy parentFreezing regularity).toReal+(fullFourierEnergy (childFreezing digit) regularity).toReal) := by
    intro digit
    exact Real.sq_sqrt (by positivity)
  have first_energy : ∀ digit, (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
      ‖𝓕 (fun value => (first digit value : ℂ)) frequency‖^2)) ≤ ENNReal.ofReal (amplitude digit^2) := by
    intro digit
    have bound := (finite_energy_amplitude_bound coefficient_finite parent_energy_finite.ne
      (children_energy_finite digit).ne).1
    apply (first_weighted digit).trans
    simpa only [coefficient, amplitude, old, parent, FrozenNewtonKernel.child, centeredFrozenNewton, mul_assoc] using bound
  have second_energy : ∀ digit, (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
      ‖𝓕 (fun value => (second digit value : ℂ)) frequency‖^2)) ≤ ENNReal.ofReal (amplitude digit^2) := by
    intro digit
    apply (second_weighted digit).trans
    simpa only [coefficient, amplitude, children, centeredFrozenNewton, mul_assoc] using
      (finite_energy_amplitude_bound coefficient_finite parent_energy_finite.ne (children_energy_finite digit).ne).2
  let couplings := fun digit => commonSourceCoupling First.Roots.pairedAddressMeasure
    (fun tail => ((old digit).value tail-origins digit)/width)
    (fun tail => ((children digit).value tail-origins digit)/width)
  have coupling_probability : ∀ digit, IsProbabilityMeasure (couplings digit) := by
    intro digit
    exact commonSourceCoupling_probability _ (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _)
  have coupling_integrable : ∀ digit, Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (couplings digit) := by
    intro digit
    exact (commonSourceCoupling_cost_of_common_approximation First.Roots.pairedAddressMeasure
      (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _)
      (root := fun _ => 0) (by simpa only [sub_zero] using old_support digit)
      (by simpa only [sub_zero] using new_support digit)).1
  have first_marginal : ∀ digit, (couplings digit).map Prod.fst =
      volume.withDensity (fun value => ENNReal.ofReal (first digit value)) := by
    intro digit
    change (commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail : ℕ → Bool × Bool => ((old digit).value tail-origins digit)/width)
      (fun tail : ℕ → Bool × Bool => ((children digit).value tail-origins digit)/width)).map Prod.fst =
        volume.withDensity (fun value => ENNReal.ofReal (first digit value))
    rw [commonSourceCoupling_fst _ (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _), ← first_law digit,
      normalizedNewtonLaw, (old digit).law_eq_paired_map]
    symm
    simpa only [Function.comp_def, id_eq] using
      (Measure.map_map (μ := First.Roots.pairedAddressMeasure)
        ((measurable_id.sub_const (origins digit)).div_const width) (old digit).value_measurable)
  have second_marginal : ∀ digit, (couplings digit).map Prod.snd =
      volume.withDensity (fun value => ENNReal.ofReal (second digit value)) := by
    intro digit
    change (commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail : ℕ → Bool × Bool => ((old digit).value tail-origins digit)/width)
      (fun tail : ℕ → Bool × Bool => ((children digit).value tail-origins digit)/width)).map Prod.snd =
        volume.withDensity (fun value => ENNReal.ofReal (second digit value))
    rw [commonSourceCoupling_snd _ (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _), ← second_law digit,
      normalizedNewtonLaw, (children digit).law_eq_paired_map]
    symm
    simpa only [Function.comp_def, id_eq] using
      (Measure.map_map (μ := First.Roots.pairedAddressMeasure)
        ((measurable_id.sub_const (origins digit)).div_const width) (children digit).value_measurable)
  let cost := ∑ digit : Bool × Bool, ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings digit
  have cost_nonnegative : 0 ≤ cost := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
  have component_cost : ∀ digit, (∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings digit) ≤ cost := by
    intro digit
    exact Finset.single_le_sum
      (f := fun other : Bool × Bool => ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings other)
      (fun other _ => integral_nonneg (μ := couplings other)
        (fun pair : ℝ × ℝ => abs_nonneg (pair.1-pair.2))) (Finset.mem_univ digit)
  obtain ⟨constant, constant_positive, transport⟩ :=
    exists_normalized_finite_mixture_transport_constant (Index := Bool × Bool) radius_positive.le
  have transport_bound := transport (fun _ => (1/4 : ℝ)) amplitude origins (fun _ => width) first second regularity cost
    (fun _ => by norm_num) (by norm_num [Fintype.sum_prod_type]) amplitude_lower (fun _ => width_positive)
    first_integrable second_integrable (fun digit => Eventually.of_forall (first_nonnegative digit))
    (fun digit => Eventually.of_forall (second_nonnegative digit)) first_support second_support
    regularity_positive regularity_le_one cost_nonnegative first_energy second_energy
    couplings coupling_probability coupling_integrable first_marginal second_marginal component_cost
  have first_physical_integrable := fun digit => integrable_physicalAffineDensity (first_integrable digit) (origins digit) width_positive
  have second_physical_integrable := fun digit => integrable_physicalAffineDensity (second_integrable digit) (origins digit) width_positive
  have first_physical_nonnegative : ∀ digit, ∀ᵐ value : ℝ,
      0 ≤ physicalAffineDensity (origins digit) width (first digit) value := by
    intro digit
    exact Eventually.of_forall (fun _ => mul_nonneg (inv_nonneg.mpr width_positive.le) (first_nonnegative digit _))
  have second_physical_nonnegative : ∀ digit, ∀ᵐ value : ℝ,
      0 ≤ physicalAffineDensity (origins digit) width (second digit) value := by
    intro digit
    exact Eventually.of_forall (fun _ => mul_nonneg (inv_nonneg.mpr width_positive.le) (second_nonnegative digit _))
  refine ⟨minimum, radius, constant, minimum_positive, radius_positive, constant_positive, first, second, ?_, ?_, ?_, coupling_integrable, ?_⟩
  · rw [parent.law_exact_digit_split parent_positive.le parent_less_one]
    have law := withDensity_finite_real_mixture (fun _ : Bool × Bool => (1/4 : ℝ))
      (fun digit => physicalAffineDensity (origins digit) width (first digit)) (fun _ => by norm_num)
      (fun digit => (first_physical_integrable digit).aestronglyMeasurable) first_physical_nonnegative
    rw [law]
    apply Finset.sum_congr rfl
    intro digit _
    rw [show ENNReal.ofReal (1/4 : ℝ) = (4 : ℝ≥0∞)⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (4 : ℝ)), ENNReal.ofReal_ofNat]]
    rw [← first_physical digit]
  · have law := withDensity_finite_real_mixture (fun _ : Bool × Bool => (1/4 : ℝ))
      (fun digit => physicalAffineDensity (origins digit) width (second digit)) (fun _ => by norm_num)
      (fun digit => (second_physical_integrable digit).aestronglyMeasurable) second_physical_nonnegative
    rw [law]
    apply Finset.sum_congr rfl
    intro digit _
    rw [show ENNReal.ofReal (1/4 : ℝ) = (4 : ℝ≥0∞)⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (4 : ℝ)), ENNReal.ofReal_ofNat]]
    rw [← second_physical digit]
  · exact fun digit => ⟨first_integrable digit, second_integrable digit, first_nonnegative digit,
      second_nonnegative digit, first_support digit, second_support digit⟩
  · simpa only [amplitude_square, coefficient, cost] using transport_bound


private theorem actual_parent_frozen_transport_fixed_geometry
    {exponent parentFreezing rho regularity : ℝ}
    (exponent_greater_one : 1 < exponent) (rho_positive : 0 < rho)
    (regularity_positive : 0 < regularity) (regularity_le_one : regularity ≤ 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (word : Fin depth → Bool × Bool)
    (childFreezing : Bool × Bool → ℝ)
    (parent_positive : 0 < parentFreezing) (parent_less_one : parentFreezing < 1)
    (children_positive : ∀ digit, 0 < childFreezing digit)
    (children_less_one : ∀ digit, childFreezing digit < 1)
    (parent_tail_small : parentFreezing^tailDepth ≤ 1/2)
    (parent_vertical_small : parentFreezing^verticalDepth ≤ 1/2)
    (children_tail_small : ∀ digit, childFreezing digit^tailDepth ≤ 1/2)
    (children_vertical_small : ∀ digit, childFreezing digit^verticalDepth ≤ 1/2)
    (parent_derivative_negative : deriv
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) parentFreezing < 0)
    (children_derivative_negative : ∀ digit, deriv
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth (depth+1) (Fin.snoc word digit))
        (childFreezing digit) < 0)
    (parent_energy_finite : fullFourierEnergy parentFreezing regularity < ⊤)
    (children_energy_finite : ∀ digit, fullFourierEnergy (childFreezing digit) regularity < ⊤)
    (requestedMinimum requestedRadius : ℝ)
    (requestedMinimum_positive : 0 < requestedMinimum) (requestedRadius_positive : 0 < requestedRadius)
    (requestedCoefficientLower :
      let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
      let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
        (depth+1) (Fin.snoc word digit) (childFreezing digit)
      let width := rho*parentFreezing^depth
      ∀ digit, requestedMinimum ≤ (parent.child digit).firstScale/width ∧
        requestedMinimum ≤ (parent.child digit).secondScale/width ∧
        requestedMinimum ≤ (children digit).firstScale/width ∧ requestedMinimum ≤ (children digit).secondScale/width)
    (requestedSupportUpper :
      let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
      let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
        (depth+1) (Fin.snoc word digit) (childFreezing digit)
      let width := rho*parentFreezing^depth
      ∀ digit, ((parent.child digit).firstScale+(parent.child digit).secondScale+
        |(children digit).affineCenter-(parent.child digit).affineCenter|+
          (children digit).firstScale+(children digit).secondScale)/width ≤ requestedRadius) :
    let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
    let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit) (childFreezing digit)
    let width := rho*parentFreezing^depth
    let origins := fun digit => (parent.child digit).affineCenter
    let couplings := fun digit => commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail => ((parent.child digit).value tail-origins digit)/width)
      (fun tail => ((children digit).value tail-origins digit)/width)
    ∃ minimum radius constant : ℝ, 0 < minimum ∧ 0 < radius ∧ 0 < constant ∧
      minimum = requestedMinimum ∧ radius = requestedRadius ∧
      constant = actualParentFreezeTransportConstant requestedRadius requestedRadius_positive.le ∧
      ∃ first second : (Bool × Bool) → ℝ → ℝ,
      parent.law = volume.withDensity (fun value => ENNReal.ofReal
        (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)) ∧
      (∑ digit : Bool × Bool, (4 : ℝ≥0∞)⁻¹ • (children digit).law) =
        volume.withDensity (fun value => ENNReal.ofReal
          (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value)) ∧
      (∀ digit, Integrable (first digit) ∧ Integrable (second digit) ∧
        (∀ value, 0 ≤ first digit value) ∧ (∀ value, 0 ≤ second digit value) ∧
        Function.support (first digit) ⊆ Icc (-radius) radius ∧
        Function.support (second digit) ⊆ Icc (-radius) radius) ∧
      (∀ digit, Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (couplings digit)) ∧
      (∫ value : ℝ, |(∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)-
        ∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value|) ≤
        constant*(∑ digit : Bool × Bool, (1/4 : ℝ)*
          (1+(2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)).toReal*
            (1+(fullFourierEnergy parentFreezing regularity).toReal+
              (fullFourierEnergy (childFreezing digit) regularity).toReal)))^(1/(2*(1+regularity)))*
          (∑ digit : Bool × Bool, ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings digit)^(regularity/(1+regularity)) := by
  classical
  dsimp only
  let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
  let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
    (depth+1) (Fin.snoc word digit) (childFreezing digit)
  let old := fun digit => parent.child digit
  let width := rho*parentFreezing^depth
  let origins := fun digit => (old digit).affineCenter
  have width_positive : 0 < width := by dsimp [width]; positivity
  have parent_scales := centered_frozen_positive_scales exponent_greater_one parent_positive parent_less_one
    horizontalDepth verticalDepth tailDepth depth word parent_tail_small parent_vertical_small parent_derivative_negative
  have old_scales : ∀ digit, 0 < (old digit).firstScale ∧ 0 < (old digit).secondScale := by
    intro digit
    dsimp [old]
    rw [child_firstScale, child_secondScale]
    exact ⟨mul_pos parent_scales.1 parent_positive, mul_pos parent_scales.2 parent_positive⟩
  have child_scales : ∀ digit, 0 < (children digit).firstScale ∧ 0 < (children digit).secondScale := by
    intro digit
    exact centered_frozen_positive_scales exponent_greater_one (children_positive digit) (children_less_one digit)
      horizontalDepth verticalDepth tailDepth (depth+1) (Fin.snoc word digit)
      (children_tail_small digit) (children_vertical_small digit) (children_derivative_negative digit)
  let minimum := requestedMinimum
  have minimum_positive : 0 < minimum := requestedMinimum_positive
  have coefficient_lower : ∀ digit,
      minimum ≤ (old digit).firstScale/width ∧ minimum ≤ (old digit).secondScale/width ∧
      minimum ≤ (children digit).firstScale/width ∧ minimum ≤ (children digit).secondScale/width := requestedCoefficientLower
  let supportTerm := fun digit => ((old digit).firstScale+(old digit).secondScale+
    |(children digit).affineCenter-origins digit|+(children digit).firstScale+(children digit).secondScale)/width
  have term_nonnegative : ∀ digit, 0 ≤ supportTerm digit := by
    intro digit
    dsimp [supportTerm]
    exact div_nonneg (by linarith [(old_scales digit).1, (old_scales digit).2,
      (child_scales digit).1, (child_scales digit).2, abs_nonneg ((children digit).affineCenter-origins digit)]) width_positive.le
  let radius := requestedRadius
  have radius_positive : 0 < radius := requestedRadius_positive
  have term_radius : ∀ digit, supportTerm digit ≤ radius := requestedSupportUpper
  have old_support : ∀ digit tail, |((old digit).value tail-origins digit)/width| ≤ radius := by
    intro digit tail
    rw [abs_div, abs_of_pos width_positive]
    apply (div_le_div_of_nonneg_right ((old digit).value_affine_support parent_positive.le parent_less_one
      (old_scales digit).1.le (old_scales digit).2.le tail) width_positive.le).trans
    apply (div_le_div_of_nonneg_right (show (old digit).firstScale+(old digit).secondScale ≤
      (old digit).firstScale+(old digit).secondScale+|(children digit).affineCenter-origins digit|+
        (children digit).firstScale+(children digit).secondScale by
      linarith [(child_scales digit).1, (child_scales digit).2,
        abs_nonneg ((children digit).affineCenter-origins digit)]) width_positive.le).trans
    exact term_radius digit
  have new_support : ∀ digit tail, |((children digit).value tail-origins digit)/width| ≤ radius := by
    intro digit tail
    have triangle := (abs_sub_le ((children digit).value tail) ((children digit).affineCenter) (origins digit)).trans
      (add_le_add ((children digit).value_affine_support (children_positive digit).le (children_less_one digit)
        (child_scales digit).1.le (child_scales digit).2.le tail)
        (le_refl |(children digit).affineCenter-origins digit|))
    rw [abs_div, abs_of_pos width_positive]
    apply (div_le_div_of_nonneg_right triangle width_positive.le).trans
    apply (div_le_div_of_nonneg_right (show (children digit).firstScale+(children digit).secondScale+
      |(children digit).affineCenter-origins digit| ≤
      (old digit).firstScale+(old digit).secondScale+|(children digit).affineCenter-origins digit|+
        (children digit).firstScale+(children digit).secondScale by
      linarith [(old_scales digit).1, (old_scales digit).2]) width_positive.le).trans
    exact term_radius digit
  have first_exists := fun digit => actual_normalized_newton_density (old digit) width_positive minimum_positive
    (coefficient_lower digit).1 (coefficient_lower digit).2.1 regularity_positive.le
    parent_energy_finite (old_support digit)
  have second_exists := fun digit => actual_normalized_newton_density (children digit) width_positive minimum_positive
    (coefficient_lower digit).2.2.1 (coefficient_lower digit).2.2.2 regularity_positive.le
    (children_energy_finite digit) (new_support digit)
  choose first first_integrable first_square first_nonnegative first_support first_law first_physical first_weighted using first_exists
  choose second second_integrable second_square second_nonnegative second_support second_law second_physical second_weighted using second_exists
  let coefficient : ℝ≥0∞ := 2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)
  have coefficient_finite : coefficient ≠ ⊤ := by dsimp [coefficient]; finiteness
  let amplitude := fun digit => Real.sqrt (1+coefficient.toReal*
    (1+(fullFourierEnergy parentFreezing regularity).toReal+(fullFourierEnergy (childFreezing digit) regularity).toReal))
  have amplitude_lower : ∀ digit, 1 ≤ amplitude digit := by
    intro digit
    dsimp [amplitude]
    apply Real.one_le_sqrt.mpr
    have product_nonnegative : 0 ≤ coefficient.toReal*
        (1+(fullFourierEnergy parentFreezing regularity).toReal+(fullFourierEnergy (childFreezing digit) regularity).toReal) := by positivity
    linarith
  have amplitude_square : ∀ digit, amplitude digit^2 = 1+coefficient.toReal*
      (1+(fullFourierEnergy parentFreezing regularity).toReal+(fullFourierEnergy (childFreezing digit) regularity).toReal) := by
    intro digit
    exact Real.sq_sqrt (by positivity)
  have first_energy : ∀ digit, (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
      ‖𝓕 (fun value => (first digit value : ℂ)) frequency‖^2)) ≤ ENNReal.ofReal (amplitude digit^2) := by
    intro digit
    have bound := (finite_energy_amplitude_bound coefficient_finite parent_energy_finite.ne
      (children_energy_finite digit).ne).1
    apply (first_weighted digit).trans
    simpa only [coefficient, amplitude, old, parent, FrozenNewtonKernel.child, centeredFrozenNewton, mul_assoc] using bound
  have second_energy : ∀ digit, (∫⁻ frequency : ℝ, ENNReal.ofReal ((1+|frequency|^(2*regularity))*
      ‖𝓕 (fun value => (second digit value : ℂ)) frequency‖^2)) ≤ ENNReal.ofReal (amplitude digit^2) := by
    intro digit
    apply (second_weighted digit).trans
    simpa only [coefficient, amplitude, children, centeredFrozenNewton, mul_assoc] using
      (finite_energy_amplitude_bound coefficient_finite parent_energy_finite.ne (children_energy_finite digit).ne).2
  let couplings := fun digit => commonSourceCoupling First.Roots.pairedAddressMeasure
    (fun tail => ((old digit).value tail-origins digit)/width)
    (fun tail => ((children digit).value tail-origins digit)/width)
  have coupling_probability : ∀ digit, IsProbabilityMeasure (couplings digit) := by
    intro digit
    exact commonSourceCoupling_probability _ (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _)
  have coupling_integrable : ∀ digit, Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (couplings digit) := by
    intro digit
    exact (commonSourceCoupling_cost_of_common_approximation First.Roots.pairedAddressMeasure
      (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _)
      (root := fun _ => 0) (by simpa only [sub_zero] using old_support digit)
      (by simpa only [sub_zero] using new_support digit)).1
  have first_marginal : ∀ digit, (couplings digit).map Prod.fst =
      volume.withDensity (fun value => ENNReal.ofReal (first digit value)) := by
    intro digit
    change (commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail : ℕ → Bool × Bool => ((old digit).value tail-origins digit)/width)
      (fun tail : ℕ → Bool × Bool => ((children digit).value tail-origins digit)/width)).map Prod.fst =
        volume.withDensity (fun value => ENNReal.ofReal (first digit value))
    rw [commonSourceCoupling_fst _ (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _), ← first_law digit,
      normalizedNewtonLaw, (old digit).law_eq_paired_map]
    symm
    simpa only [Function.comp_def, id_eq] using
      (Measure.map_map (μ := First.Roots.pairedAddressMeasure)
        ((measurable_id.sub_const (origins digit)).div_const width) (old digit).value_measurable)
  have second_marginal : ∀ digit, (couplings digit).map Prod.snd =
      volume.withDensity (fun value => ENNReal.ofReal (second digit value)) := by
    intro digit
    change (commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail : ℕ → Bool × Bool => ((old digit).value tail-origins digit)/width)
      (fun tail : ℕ → Bool × Bool => ((children digit).value tail-origins digit)/width)).map Prod.snd =
        volume.withDensity (fun value => ENNReal.ofReal (second digit value))
    rw [commonSourceCoupling_snd _ (((old digit).value_measurable.sub_const _).div_const _)
      (((children digit).value_measurable.sub_const _).div_const _), ← second_law digit,
      normalizedNewtonLaw, (children digit).law_eq_paired_map]
    symm
    simpa only [Function.comp_def, id_eq] using
      (Measure.map_map (μ := First.Roots.pairedAddressMeasure)
        ((measurable_id.sub_const (origins digit)).div_const width) (children digit).value_measurable)
  let cost := ∑ digit : Bool × Bool, ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings digit
  have cost_nonnegative : 0 ≤ cost := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
  have component_cost : ∀ digit, (∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings digit) ≤ cost := by
    intro digit
    exact Finset.single_le_sum
      (f := fun other : Bool × Bool => ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings other)
      (fun other _ => integral_nonneg (μ := couplings other)
        (fun pair : ℝ × ℝ => abs_nonneg (pair.1-pair.2))) (Finset.mem_univ digit)
  let constant := actualParentFreezeTransportConstant requestedRadius requestedRadius_positive.le
  have constant_spec := Classical.choose_spec
    (exists_normalized_finite_mixture_transport_constant (Index := Bool × Bool) requestedRadius_positive.le)
  have constant_positive : 0 < constant := constant_spec.1
  have transport := constant_spec.2
  have transport_bound := transport (fun _ => (1/4 : ℝ)) amplitude origins (fun _ => width) first second regularity cost
    (fun _ => by norm_num) (by norm_num [Fintype.sum_prod_type]) amplitude_lower (fun _ => width_positive)
    first_integrable second_integrable (fun digit => Eventually.of_forall (first_nonnegative digit))
    (fun digit => Eventually.of_forall (second_nonnegative digit)) first_support second_support
    regularity_positive regularity_le_one cost_nonnegative first_energy second_energy
    couplings coupling_probability coupling_integrable first_marginal second_marginal component_cost
  have first_physical_integrable := fun digit => integrable_physicalAffineDensity (first_integrable digit) (origins digit) width_positive
  have second_physical_integrable := fun digit => integrable_physicalAffineDensity (second_integrable digit) (origins digit) width_positive
  have first_physical_nonnegative : ∀ digit, ∀ᵐ value : ℝ,
      0 ≤ physicalAffineDensity (origins digit) width (first digit) value := by
    intro digit
    exact Eventually.of_forall (fun _ => mul_nonneg (inv_nonneg.mpr width_positive.le) (first_nonnegative digit _))
  have second_physical_nonnegative : ∀ digit, ∀ᵐ value : ℝ,
      0 ≤ physicalAffineDensity (origins digit) width (second digit) value := by
    intro digit
    exact Eventually.of_forall (fun _ => mul_nonneg (inv_nonneg.mpr width_positive.le) (second_nonnegative digit _))
  refine ⟨minimum, radius, constant, minimum_positive, radius_positive, constant_positive, rfl, rfl, rfl, first, second, ?_, ?_, ?_, coupling_integrable, ?_⟩
  · rw [parent.law_exact_digit_split parent_positive.le parent_less_one]
    have law := withDensity_finite_real_mixture (fun _ : Bool × Bool => (1/4 : ℝ))
      (fun digit => physicalAffineDensity (origins digit) width (first digit)) (fun _ => by norm_num)
      (fun digit => (first_physical_integrable digit).aestronglyMeasurable) first_physical_nonnegative
    rw [law]
    apply Finset.sum_congr rfl
    intro digit _
    rw [show ENNReal.ofReal (1/4 : ℝ) = (4 : ℝ≥0∞)⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (4 : ℝ)), ENNReal.ofReal_ofNat]]
    rw [← first_physical digit]
  · have law := withDensity_finite_real_mixture (fun _ : Bool × Bool => (1/4 : ℝ))
      (fun digit => physicalAffineDensity (origins digit) width (second digit)) (fun _ => by norm_num)
      (fun digit => (second_physical_integrable digit).aestronglyMeasurable) second_physical_nonnegative
    rw [law]
    apply Finset.sum_congr rfl
    intro digit _
    rw [show ENNReal.ofReal (1/4 : ℝ) = (4 : ℝ≥0∞)⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (4 : ℝ)), ENNReal.ofReal_ofNat]]
    rw [← second_physical digit]
  · exact fun digit => ⟨first_integrable digit, second_integrable digit, first_nonnegative digit,
      second_nonnegative digit, first_support digit, second_support digit⟩
  · simpa only [amplitude_square, coefficient, cost, constant, actualParentFreezeTransportConstant,
      couplings, origins, old, parent, children, width] using transport_bound

private theorem actual_parent_uniform_geometry
    {exponent lower discrepancyBound slope derivativeBound parentFreezing rho : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower)
    (discrepancy_nonnegative : 0 ≤ discrepancyBound) (slope_positive : 0 < slope)
    (derivative_positive : 0 < derivativeBound) (rho_positive : 0 < rho) (rho_small : rho ≤ 1/4)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (word : Fin depth → Bool × Bool)
    (childFreezing : Bool × Bool → ℝ)
    (parent_lower : lower ≤ parentFreezing) (parent_less_one : parentFreezing < 1)
    (children_lower : ∀ digit, lower ≤ childFreezing digit) (children_less_one : ∀ digit, childFreezing digit < 1)
    (parent_tail : rho/2 ≤ parentFreezing^tailDepth ∧ parentFreezing^tailDepth ≤ 2*rho)
    (children_tail : ∀ digit, rho/2 ≤ childFreezing digit^tailDepth ∧ childFreezing digit^tailDepth ≤ 2*rho)
    (parent_vertical_small : parentFreezing^verticalDepth ≤ 1/2)
    (children_vertical_small : ∀ digit, childFreezing digit^verticalDepth ≤ 1/2)
    (phase_bound : |(verticalDepth : ℝ)-exponent*horizontalDepth| ≤ discrepancyBound)
    (parent_derivative : deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) parentFreezing ≤ -slope)
    (parent_derivative_bound : |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) parentFreezing| ≤ derivativeBound)
    (children_derivative : ∀ digit, deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit)) (childFreezing digit) ≤ -slope)
    (children_derivative_bound : ∀ digit, |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit)) (childFreezing digit)| ≤ derivativeBound)
    (powers_comparable : ∀ digit, (1/2)*parentFreezing^depth ≤ childFreezing digit^depth ∧
      childFreezing digit^depth ≤ 2*parentFreezing^depth)
    (center_shift :
      let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
      ∀ digit, |(centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth (depth+1)
        (Fin.snoc word digit) (childFreezing digit)).affineCenter-(parent.child digit).affineCenter| ≤ rho*parentFreezing^depth) :
    let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
    let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit) (childFreezing digit)
    let width := rho*parentFreezing^depth
    (∀ digit, actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (parent.child digit).firstScale/width ∧
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (parent.child digit).secondScale/width ∧
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (children digit).firstScale/width ∧
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (children digit).secondScale/width) ∧
    (∀ digit, ((parent.child digit).firstScale+(parent.child digit).secondScale+
      |(children digit).affineCenter-(parent.child digit).affineCenter|+
        (children digit).firstScale+(children digit).secondScale)/width ≤
      actualParentUniformRadius exponent lower discrepancyBound slope) := by
  classical
  dsimp only
  let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
  let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
    (depth+1) (Fin.snoc word digit) (childFreezing digit)
  let width := rho*parentFreezing^depth
  let firstLower := exponent*(1/2 : ℝ)^(exponent-1)/(2*derivativeBound)
  let secondLower := exponent*lower^discrepancyBound*(1/2 : ℝ)^(exponent-1)/(2*derivativeBound)
  let coefficientMinimum := min firstLower secondLower
  let scaleUpper := 2*exponent*(1+lower^(-discrepancyBound))/slope
  have exponent_positive : 0 < exponent := by linarith
  have parent_positive := lower_positive.trans_le parent_lower
  have children_positive := fun digit => lower_positive.trans_le (children_lower digit)
  have width_positive : 0 < width := by dsimp [width]; positivity
  have firstLower_positive : 0 < firstLower := by dsimp [firstLower]; positivity
  have secondLower_positive : 0 < secondLower := by dsimp [secondLower]; positivity
  have coefficientMinimum_positive : 0 < coefficientMinimum := lt_min firstLower_positive secondLower_positive
  have scaleUpper_positive : 0 < scaleUpper := by dsimp [scaleUpper]; positivity
  have parent_bounds := centeredFrozenNewton_scale_bounds exponent_greater_one parent_positive parent_less_one
    lower_positive parent_lower rho_positive.le discrepancy_nonnegative slope_positive derivative_positive
    horizontalDepth verticalDepth tailDepth depth (prefixFreshTail word (fun _ => (false, false)))
    (by linarith [parent_tail.2]) parent_vertical_small parent_tail.1 parent_tail.2 phase_bound
    (by simpa only [prefixFreshTail_word] using parent_derivative)
    (by simpa only [prefixFreshTail_word] using parent_derivative_bound)
  have parent_bounds' : (firstLower*width ≤ parent.firstScale ∧ parent.firstScale ≤ (2*exponent/slope)*width) ∧
      (secondLower*width ≤ parent.secondScale ∧ parent.secondScale ≤ (2*exponent*lower^(-discrepancyBound)/slope)*width) := by
    simpa only [prefixFreshTail_word, parent, firstLower, secondLower, width, mul_assoc] using parent_bounds
  have children_bounds : ∀ digit,
      (firstLower*(rho*childFreezing digit^(depth+1)) ≤ (children digit).firstScale ∧
        (children digit).firstScale ≤ (2*exponent/slope)*(rho*childFreezing digit^(depth+1))) ∧
      (secondLower*(rho*childFreezing digit^(depth+1)) ≤ (children digit).secondScale ∧
        (children digit).secondScale ≤ (2*exponent*lower^(-discrepancyBound)/slope)*(rho*childFreezing digit^(depth+1))) := by
    intro digit
    have bounds := centeredFrozenNewton_scale_bounds exponent_greater_one (children_positive digit) (children_less_one digit)
      lower_positive (children_lower digit) rho_positive.le discrepancy_nonnegative slope_positive derivative_positive
      horizontalDepth verticalDepth tailDepth (depth+1) (prefixFreshTail (Fin.snoc word digit) (fun _ => (false, false)))
      (by linarith [(children_tail digit).2]) (children_vertical_small digit)
      (children_tail digit).1 (children_tail digit).2 phase_bound
      (by simpa only [prefixFreshTail_word] using children_derivative digit)
      (by simpa only [prefixFreshTail_word] using children_derivative_bound digit)
    simpa only [prefixFreshTail_word, children, firstLower, secondLower, mul_assoc] using bounds
  have lower_pair : ∀ digit coefficient parentScale childScale,
      coefficientMinimum ≤ coefficient → coefficient*width ≤ parentScale →
      coefficient*(rho*childFreezing digit^(depth+1)) ≤ childScale →
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ parentScale*parentFreezing/width ∧
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ childScale/width := by
    intro digit coefficient parentScale childScale coefficient_lower parent_bound child_bound
    have coefficient_positive := coefficientMinimum_positive.trans_le coefficient_lower
    have minimum_le : actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ coefficient*lower/2 := by
      change lower*coefficientMinimum/2 ≤ coefficient*lower/2
      exact div_le_div_of_nonneg_right
        ((mul_le_mul_of_nonneg_left coefficient_lower lower_positive.le).trans_eq (mul_comm _ _)) (by norm_num)
    have parent_factor : actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ coefficient*parentFreezing := by
      apply minimum_le.trans
      have half_lower : lower/2 ≤ parentFreezing := by linarith
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left half_lower coefficient_positive.le
    have power_lower : (lower/2)*parentFreezing^depth ≤ childFreezing digit^(depth+1) := by
      calc
        _ = ((1/2)*parentFreezing^depth)*lower := by ring
        _ ≤ childFreezing digit^depth*childFreezing digit :=
          mul_le_mul (powers_comparable digit).1 (children_lower digit) lower_positive.le
            (pow_nonneg (children_positive digit).le depth)
        _ = _ := (pow_succ _ _).symm
    constructor
    · apply (le_div_iff₀ width_positive).mpr
      calc
        _ ≤ (coefficient*parentFreezing)*width := mul_le_mul_of_nonneg_right parent_factor width_positive.le
        _ = (coefficient*width)*parentFreezing := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right parent_bound parent_positive.le
    · apply (le_div_iff₀ width_positive).mpr
      calc
        _ ≤ (coefficient*lower/2)*width := mul_le_mul_of_nonneg_right minimum_le width_positive.le
        _ = coefficient*rho*((lower/2)*parentFreezing^depth) := by dsimp [width]; ring
        _ ≤ coefficient*rho*childFreezing digit^(depth+1) :=
          mul_le_mul_of_nonneg_left power_lower (mul_nonneg coefficient_positive.le rho_positive.le)
        _ = coefficient*(rho*childFreezing digit^(depth+1)) := by ring
        _ ≤ _ := child_bound
  have coefficient_lower : ∀ digit,
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (parent.child digit).firstScale/width ∧
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (parent.child digit).secondScale/width ∧
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (children digit).firstScale/width ∧
      actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ≤ (children digit).secondScale/width := by
    intro digit
    have first := lower_pair digit firstLower parent.firstScale (children digit).firstScale (min_le_left _ _)
      parent_bounds'.1.1 (children_bounds digit).1.1
    have second := lower_pair digit secondLower parent.secondScale (children digit).secondScale (min_le_right _ _)
      parent_bounds'.2.1 (children_bounds digit).2.1
    rw [child_firstScale, child_secondScale]
    exact ⟨first.1, second.1, first.2, second.2⟩
  refine ⟨coefficient_lower, ?_⟩
  intro digit
  have parent_sum : parent.firstScale+parent.secondScale ≤ scaleUpper*width := by
    have identity : (2*exponent/slope)+(2*exponent*lower^(-discrepancyBound)/slope) = scaleUpper := by dsimp [scaleUpper]; ring
    rw [← identity, add_mul]
    exact add_le_add parent_bounds'.1.2 parent_bounds'.2.2
  have old_sum : (parent.child digit).firstScale+(parent.child digit).secondScale ≤ scaleUpper*width := by
    rw [child_firstScale, child_secondScale, ← add_mul]
    exact (mul_le_mul_of_nonneg_right parent_sum parent_positive.le).trans
      (mul_le_of_le_one_right (mul_nonneg scaleUpper_positive.le width_positive.le) parent_less_one.le)
  have child_sum : (children digit).firstScale+(children digit).secondScale ≤ 2*scaleUpper*width := by
    have identity : (2*exponent/slope)+(2*exponent*lower^(-discrepancyBound)/slope) = scaleUpper := by dsimp [scaleUpper]; ring
    have raw : (children digit).firstScale+(children digit).secondScale ≤
        scaleUpper*(rho*childFreezing digit^(depth+1)) := by
      rw [← identity, add_mul]
      exact add_le_add (children_bounds digit).1.2 (children_bounds digit).2.2
    have power_upper : childFreezing digit^(depth+1) ≤ 2*parentFreezing^depth := by
      rw [pow_succ]
      exact (mul_le_of_le_one_right (pow_nonneg (children_positive digit).le _) (children_less_one digit).le).trans
        (powers_comparable digit).2
    apply raw.trans
    have bound := mul_le_mul_of_nonneg_left power_upper (mul_nonneg scaleUpper_positive.le rho_positive.le)
    simpa only [width, mul_assoc, mul_left_comm, mul_comm] using bound
  apply (div_le_iff₀ width_positive).mpr
  change _ ≤ (3*scaleUpper+1)*width
  have shift := center_shift digit
  change |(children digit).affineCenter-(parent.child digit).affineCenter| ≤ width at shift
  nlinarith

/-- The actual parent replacement uses one positive minimum scale, one support
radius and one transport constant determined solely by the fixed band and
uniform derivative bounds. The displayed constants do not depend on the
initial depth, prefix depth, paired word or selected freezing points. -/
theorem actual_parent_uniform_frozen_mixture_transport
    {exponent lower discrepancyBound slope derivativeBound parentFreezing rho regularity : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower)
    (discrepancy_nonnegative : 0 ≤ discrepancyBound) (slope_positive : 0 < slope)
    (derivative_positive : 0 < derivativeBound) (rho_positive : 0 < rho) (rho_small : rho ≤ 1/4)
    (regularity_positive : 0 < regularity) (regularity_le_one : regularity ≤ 1)
    (horizontalDepth verticalDepth tailDepth depth : ℕ) (word : Fin depth → Bool × Bool)
    (childFreezing : Bool × Bool → ℝ)
    (parent_lower : lower ≤ parentFreezing) (parent_less_one : parentFreezing < 1)
    (children_lower : ∀ digit, lower ≤ childFreezing digit) (children_less_one : ∀ digit, childFreezing digit < 1)
    (parent_tail : rho/2 ≤ parentFreezing^tailDepth ∧ parentFreezing^tailDepth ≤ 2*rho)
    (children_tail : ∀ digit, rho/2 ≤ childFreezing digit^tailDepth ∧ childFreezing digit^tailDepth ≤ 2*rho)
    (parent_vertical_small : parentFreezing^verticalDepth ≤ 1/2)
    (children_vertical_small : ∀ digit, childFreezing digit^verticalDepth ≤ 1/2)
    (phase_bound : |(verticalDepth : ℝ)-exponent*horizontalDepth| ≤ discrepancyBound)
    (parent_derivative : deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) parentFreezing ≤ -slope)
    (parent_derivative_bound : |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) parentFreezing| ≤ derivativeBound)
    (children_derivative : ∀ digit, deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit)) (childFreezing digit) ≤ -slope)
    (children_derivative_bound : ∀ digit, |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit)) (childFreezing digit)| ≤ derivativeBound)
    (powers_comparable : ∀ digit, (1/2)*parentFreezing^depth ≤ childFreezing digit^depth ∧
      childFreezing digit^depth ≤ 2*parentFreezing^depth)
    (center_shift :
      let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
      ∀ digit, |(centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth (depth+1)
        (Fin.snoc word digit) (childFreezing digit)).affineCenter-(parent.child digit).affineCenter| ≤ rho*parentFreezing^depth)
    (parent_energy_finite : fullFourierEnergy parentFreezing regularity < ⊤)
    (children_energy_finite : ∀ digit, fullFourierEnergy (childFreezing digit) regularity < ⊤) :
    let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word parentFreezing
    let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit) (childFreezing digit)
    let width := rho*parentFreezing^depth
    let origins := fun digit => (parent.child digit).affineCenter
    let couplings := fun digit => commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail => ((parent.child digit).value tail-origins digit)/width)
      (fun tail => ((children digit).value tail-origins digit)/width)
    ∃ minimum radius constant : ℝ, 0 < minimum ∧ 0 < radius ∧ 0 < constant ∧
      minimum = actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ∧ radius = (actualParentUniformRadius exponent lower discrepancyBound slope) ∧
      constant = actualParentFreezeTransportConstant (actualParentUniformRadius exponent lower discrepancyBound slope) (actualParentUniformRadius_positive exponent_greater_one lower_positive slope_positive).le ∧
      ∃ first second : (Bool × Bool) → ℝ → ℝ,
      parent.law = volume.withDensity (fun value => ENNReal.ofReal
        (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)) ∧
      (∑ digit : Bool × Bool, (4 : ℝ≥0∞)⁻¹ • (children digit).law) =
        volume.withDensity (fun value => ENNReal.ofReal
          (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value)) ∧
      (∀ digit, Integrable (first digit) ∧ Integrable (second digit) ∧
        (∀ value, 0 ≤ first digit value) ∧ (∀ value, 0 ≤ second digit value) ∧
        Function.support (first digit) ⊆ Icc (-radius) radius ∧
        Function.support (second digit) ⊆ Icc (-radius) radius) ∧
      (∀ digit, Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (couplings digit)) ∧
      (∫ value : ℝ, |(∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)-
        ∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value|) ≤
        constant*(∑ digit : Bool × Bool, (1/4 : ℝ)*
          (1+(2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)).toReal*
            (1+(fullFourierEnergy parentFreezing regularity).toReal+
              (fullFourierEnergy (childFreezing digit) regularity).toReal)))^(1/(2*(1+regularity)))*
          (∑ digit : Bool × Bool, ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂couplings digit)^(regularity/(1+regularity)) := by
  have parent_positive := lower_positive.trans_le parent_lower
  have children_positive := fun digit => lower_positive.trans_le (children_lower digit)
  obtain ⟨coefficient_lower, support_upper⟩ := actual_parent_uniform_geometry exponent_greater_one lower_positive
    discrepancy_nonnegative slope_positive derivative_positive rho_positive rho_small horizontalDepth verticalDepth tailDepth depth word
    childFreezing parent_lower parent_less_one children_lower children_less_one parent_tail children_tail
    parent_vertical_small children_vertical_small phase_bound parent_derivative parent_derivative_bound
    children_derivative children_derivative_bound powers_comparable center_shift
  exact actual_parent_frozen_transport_fixed_geometry exponent_greater_one rho_positive regularity_positive regularity_le_one
    horizontalDepth verticalDepth tailDepth depth word childFreezing parent_positive parent_less_one children_positive children_less_one
    (by linarith [parent_tail.2]) parent_vertical_small (fun digit => by linarith [(children_tail digit).2]) children_vertical_small
    (by linarith) (fun digit => by have bound := children_derivative digit; linarith)
    parent_energy_finite children_energy_finite
    (actualParentUniformMinimum exponent lower discrepancyBound derivativeBound)
    (actualParentUniformRadius exponent lower discrepancyBound slope)
    (actualParentUniformMinimum_positive exponent_greater_one lower_positive derivative_positive)
    (actualParentUniformRadius_positive exponent_greater_one lower_positive slope_positive)
    coefficient_lower support_upper

/-- Actual derivatives and actual interval-selected freezing points imply
both the full shifted-center comparison and the small normalized coupling
cost. No Newton-error or transport-cost conclusion is assumed. -/
theorem actual_parent_center_and_cost_of_derivatives
    {exponent lower upper rho normalizedBound mixedBound secondBound displacementConstant slope : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower)
    (upper_positive : 0 < upper) (upper_less_one : upper < 1) (rho_positive : 0 < rho)
    (normalized_nonnegative : 0 ≤ normalizedBound) (mixed_nonnegative : 0 ≤ mixedBound)
    (second_nonnegative : 0 ≤ secondBound) (displacement_nonnegative : 0 ≤ displacementConstant)
    (slope_positive : 0 < slope) (horizontalDepth verticalDepth tailDepth : ℕ) (vertical_large : 1 ≤ verticalDepth)
    (root : (ℕ → Bool × Bool) → ℝ) (freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
    (prefix_displacement : ∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
      (∀ index < depth, first index = second index) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (freezing_mem : ∀ depth word, freezing depth word ∈
      centeredFreezingInterval root depth displacementConstant rho upper word)
    (freezing_band : ∀ depth word, freezing depth word ∈ Icc lower upper)
    (band : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      0 < parameter ∧ parameter < 1 ∧ parameter^tailDepth ≤ 1/2 ∧ parameter^verticalDepth ≤ 1/2)
    (tail_rho : ∀ depth word, freezing depth word^tailDepth ≤ 2*rho)
    (normalized_bound : ∀ depth word, (verticalDepth : ℝ)^2*
      ((freezing depth word)^(-exponent*(horizontalDepth : ℝ))*((freezing depth word)^verticalDepth)^2) ≤ normalizedBound)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (derivative_negative : ∀ depth word, deriv
      (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word) (freezing depth word) ≤ -slope)
    (second_bound : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      |centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits) parameter| ≤ secondBound)
    (mixed_bound : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) parameter-
        deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits)) parameter| ≤
          mixedBound*rho*(((tailDepth+depth+1 : ℕ) : ℝ))*upper^depth)
    (smallness : ∀ depth, 3*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
      rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth ≤ 1) :
    ∀ (depth : ℕ) (word : Fin depth → Bool × Bool) (digit : Bool × Bool),
    let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)
    let child := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth (depth+1)
      (Fin.snoc word digit) (freezing (depth+1) (Fin.snoc word digit))
    let width := rho*(freezing depth word)^depth
    let coupling := commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail => ((parent.child digit).value tail-(parent.child digit).affineCenter)/width)
      (fun tail => (child.value tail-(parent.child digit).affineCenter)/width)
    |child.affineCenter-(parent.child digit).affineCenter| ≤ width ∧
      Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) coupling ∧
      (∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂coupling) ≤
        3*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
          rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth := by
  classical
  let errorConstant := actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope
  have exponent_positive : 0 < exponent := by linarith
  have error_nonnegative : 0 ≤ errorConstant := by
    dsimp [errorConstant, actualParentNewtonErrorConstant]
    positivity
  have errors : ∀ (depth : ℕ) (word : Fin depth → Bool × Bool) tail,
      |root (prefixFreshTail word tail)-
        (centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)).value tail| ≤
      errorConstant*rho^2*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^depth)^2 := by
    intro depth word
    apply actual_prefix_newton_estimate exponent_greater_one horizontalDepth verticalDepth tailDepth depth word root
      rho_positive.le normalized_nonnegative mixed_nonnegative second_nonnegative
      (show 0 ≤ 2*displacementConstant by positivity) slope_positive vertical_large
    · intro tail parameter membership
      apply band depth (prefixFreshTail word tail) parameter
      simpa only [prefixFreshTail_word] using membership
    · exact (freezing_band depth word).2
    · exact tail_rho depth word
    · exact normalized_bound depth word
    · exact root_zero
    · exact derivative_negative depth word
    · intro tail parameter membership
      apply second_bound depth (prefixFreshTail word tail) parameter
      simpa only [prefixFreshTail_word] using membership
    · intro tail parameter membership
      apply mixed_bound depth (prefixFreshTail word tail) parameter
      simpa only [prefixFreshTail_word] using membership
    · intro tail
      have displacement := centered_freezing_root_distance root depth (prefix_displacement depth)
        (freezing depth) (freezing_mem depth) (prefixFreshTail word tail)
      simpa only [prefixFreshTail_word, mul_assoc] using displacement
  intro depth word digit
  dsimp only
  let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)
  let child := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth (depth+1)
    (Fin.snoc word digit) (freezing (depth+1) (Fin.snoc word digit))
  let width := rho*(freezing depth word)^depth
  let commonRoot := fun tail => root (prefixFreshTail (Fin.snoc word digit) tail)
  let parentError := errorConstant*rho^2*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^depth)^2
  let childError := errorConstant*rho^2*(((tailDepth+(depth+1)+1 : ℕ) : ℝ))*(upper^(depth+1))^2
  have parent_positive := lower_positive.trans_le (freezing_band depth word).1
  have parent_less_one := (freezing_band depth word).2.trans_lt upper_less_one
  have width_positive : 0 < width := by dsimp [width]; positivity
  have first_error : ∀ tail, |(parent.child digit).value tail-commonRoot tail| ≤ parentError := by
    intro tail
    have bound := errors depth word (prependNewtonDigit digit tail)
    rw [← prefixFreshTail_snoc word digit tail] at bound
    have value := parent.child_value parent_positive.le parent_less_one digit tail
    rw [← value] at bound
    rw [abs_sub_comm] at bound
    exact bound
  have second_error : ∀ tail, |child.value tail-commonRoot tail| ≤ childError := by
    intro tail
    have bound := errors (depth+1) (Fin.snoc word digit) tail
    rw [abs_sub_comm] at bound
    exact bound
  have power_bound : (upper^(depth+1))^2 ≤ (upper^depth)^2 := by
    rw [pow_succ upper depth, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ upper_positive.le upper_less_one.le (n := 2))
  have number_bound : (((tailDepth+(depth+1)+1 : ℕ) : ℝ)) ≤ 2*(((tailDepth+depth+1 : ℕ) : ℝ)) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) tailDepth, Nat.cast_nonneg (α := ℝ) depth]
  have child_error_bound : childError ≤ 2*parentError := by
    have multiplied := mul_le_mul number_bound power_bound (sq_nonneg _) (by positivity)
    have scaled := mul_le_mul_of_nonneg_left multiplied (show 0 ≤ errorConstant*rho^2 by positivity)
    dsimp [childError, parentError]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using scaled
  have sum_bound : parentError+childError ≤
      (3*errorConstant)*rho^2*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^depth)^2 := by
    dsimp [parentError] at child_error_bound ⊢
    linarith
  have width_lower : 1*rho*lower^depth ≤ width := by
    dsimp [width]
    simpa only [one_mul] using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ lower_positive.le (freezing_band depth word).1 depth) rho_positive.le
  have normalized_cost : (parentError+childError)/width ≤
      3*errorConstant*rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth := by
    simpa only [div_one] using newton_normalized_transport_cost depth
      (constant := 3*errorConstant) (minimumScale := 1) (by positivity) (by norm_num)
      rho_positive lower_positive (by positivity) sum_bound width_lower
  have sum_small : parentError+childError ≤ width :=
    (div_le_one width_positive).mp (normalized_cost.trans (smallness depth))
  have center_bound : |child.affineCenter-(parent.child digit).affineCenter| ≤ width := by
    rw [← kernel_value_zero child, ← kernel_value_zero (parent.child digit)]
    have triangle := abs_sub_le (child.value (fun _ => (false, false)))
      (commonRoot (fun _ => (false, false))) ((parent.child digit).value (fun _ => (false, false)))
    rw [abs_sub_comm (commonRoot _) ((parent.child digit).value _)] at triangle
    linarith [first_error (fun _ => (false, false)), second_error (fun _ => (false, false))]
  obtain ⟨integrable, cost⟩ := affine_common_source_cost First.Roots.pairedAddressMeasure
    ((parent.child digit).affineCenter) width_positive
    (parent.child digit).value_measurable child.value_measurable first_error second_error
  exact ⟨center_bound, integrable, cost.trans normalized_cost⟩

/-- The power-comparison threshold depends only on the fixed contraction
band and prefix displacement constant. The freezing points are the actual
interval-selected parameters of the root tree. -/
theorem actual_selected_freezing_power_comparison
    {lower upper displacementConstant : ℝ}
    (lower_positive : 0 < lower) (upper_positive : 0 < upper) (upper_less_one : upper < 1)
    (square_less : upper*upper < lower) (displacement_nonnegative : 0 ≤ displacementConstant) :
    ∃ powerConstant : ℝ, 0 < powerConstant ∧
      ∀ (rho : ℝ) (root : (ℕ → Bool × Bool) → ℝ)
        (freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ),
      0 < rho → powerConstant*rho ≤ 1/2 →
      (∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
        (∀ index < depth, first index = second index) →
        |root first-root second| ≤ displacementConstant*rho*upper^depth) →
      (∀ depth word, freezing depth word ∈ centeredFreezingInterval root depth displacementConstant rho upper word) →
      (∀ depth word, freezing depth word ∈ Icc lower upper) →
      ∀ (depth : ℕ) (word : Fin depth → Bool × Bool) (digit : Bool × Bool),
        (1/2)*(freezing depth word)^depth ≤ (freezing (depth+1) (Fin.snoc word digit))^depth ∧
          (freezing (depth+1) (Fin.snoc word digit))^depth ≤ 2*(freezing depth word)^depth := by
  obtain ⟨powerConstant, constant_positive, relative⟩ := freezing_power_relative_bound lower_positive upper_positive
    square_less (show 0 ≤ 4*displacementConstant by positivity)
  refine ⟨powerConstant, constant_positive, ?_⟩
  intro rho root freezing rho_positive small prefix_displacement freezing_mem freezing_band depth word digit
  have prefix_parent : (fun index : Fin depth =>
      prefixFreshTail (Fin.snoc word digit) (fun _ => (false, false)) index) = word := by
    rw [prefixFreshTail_snoc]
    exact prefixFreshTail_word word _
  have displacement := centered_adjacent_freezing_distance root displacement_nonnegative rho_positive.le upper_positive.le
    upper_less_one.le prefix_displacement freezing freezing_mem depth
      (prefixFreshTail (Fin.snoc word digit) (fun _ => (false, false)))
  have displacement' : |freezing depth word-freezing (depth+1) (Fin.snoc word digit)| ≤
      (4*displacementConstant)*rho*upper^depth := by
    simpa only [prefix_parent, prefixFreshTail_word, mul_assoc] using displacement
  have relative_bound := relative depth rho (freezing depth word) (freezing (depth+1) (Fin.snoc word digit))
    rho_positive.le (freezing_band depth word) (freezing_band (depth+1) (Fin.snoc word digit)) displacement'
  have power_nonnegative := pow_nonneg (lower_positive.le.trans (freezing_band depth word).1) depth
  have absolute := abs_le.mp (relative_bound.trans (mul_le_mul_of_nonneg_right small power_nonnegative))
  constructor <;> linarith [absolute.1, absolute.2]

def actualSelectedPowerConstant {lower upper displacementConstant : ℝ}
    (lower_positive : 0 < lower) (upper_positive : 0 < upper) (upper_less_one : upper < 1)
    (square_less : upper*upper < lower) (displacement_nonnegative : 0 ≤ displacementConstant) : ℝ :=
  Classical.choose (actual_selected_freezing_power_comparison lower_positive upper_positive upper_less_one square_less displacement_nonnegative)

/-- Actual finite-energy interval selections and actual derivative bounds
supply the per-parent L1 replacement estimate with constants independent of
initial depth, refinement depth, prefix and selected points. -/
theorem actual_parent_uniform_increment_from_selected_points
    {exponent lower upper discrepancyBound slope derivativeBound rho regularity
      normalizedBound mixedBound secondBound displacementConstant : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower)
    (upper_positive : 0 < upper) (upper_less_one : upper < 1) (square_less : upper*upper < lower)
    (discrepancy_nonnegative : 0 ≤ discrepancyBound) (slope_positive : 0 < slope)
    (derivative_positive : 0 < derivativeBound) (rho_positive : 0 < rho) (rho_small : rho ≤ 1/4)
    (regularity_positive : 0 < regularity) (regularity_le_one : regularity ≤ 1)
    (normalized_nonnegative : 0 ≤ normalizedBound) (mixed_nonnegative : 0 ≤ mixedBound)
    (second_nonnegative : 0 ≤ secondBound) (displacement_nonnegative : 0 ≤ displacementConstant)
    (power_small : actualSelectedPowerConstant lower_positive upper_positive upper_less_one square_less displacement_nonnegative*rho ≤ 1/2)
    (horizontalDepth verticalDepth tailDepth : ℕ) (vertical_large : 1 ≤ verticalDepth)
    (root : (ℕ → Bool × Bool) → ℝ) (freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
    (prefix_displacement : ∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
      (∀ index < depth, first index = second index) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (freezing_mem : ∀ depth word, freezing depth word ∈ centeredFreezingInterval root depth displacementConstant rho upper word)
    (freezing_band : ∀ depth word, freezing depth word ∈ Icc lower upper)
    (band : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      0 < parameter ∧ parameter < 1 ∧ parameter^tailDepth ≤ 1/2 ∧ parameter^verticalDepth ≤ 1/2)
    (tail_comparable : ∀ depth word, rho/2 ≤ (freezing depth word)^tailDepth ∧ (freezing depth word)^tailDepth ≤ 2*rho)
    (phase_bound : |(verticalDepth : ℝ)-exponent*horizontalDepth| ≤ discrepancyBound)
    (normalized_bound : ∀ depth word, (verticalDepth : ℝ)^2*
      ((freezing depth word)^(-exponent*(horizontalDepth : ℝ))*((freezing depth word)^verticalDepth)^2) ≤ normalizedBound)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (derivative_negative : ∀ depth word, deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word)
      (freezing depth word) ≤ -slope)
    (derivative_bound : ∀ depth word, |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word)
      (freezing depth word)| ≤ derivativeBound)
    (second_bound : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      |centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits) parameter| ≤ secondBound)
    (mixed_bound : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) parameter-
        deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits)) parameter| ≤
          mixedBound*rho*(((tailDepth+depth+1 : ℕ) : ℝ))*upper^depth)
    (finite_energy : ∀ depth word, fullFourierEnergy (freezing depth word) regularity < ⊤)
    (smallness : ∀ depth, 3*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
      rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth ≤ 1) :
    ∀ (depth : ℕ) (word : Fin depth → Bool × Bool),
    let parent := centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)
    let children := fun digit => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth
      (depth+1) (Fin.snoc word digit) (freezing (depth+1) (Fin.snoc word digit))
    let width := rho*(freezing depth word)^depth
    let origins := fun digit => (parent.child digit).affineCenter
    let couplings := fun digit => commonSourceCoupling First.Roots.pairedAddressMeasure
      (fun tail => ((parent.child digit).value tail-origins digit)/width)
      (fun tail => ((children digit).value tail-origins digit)/width)
    ∃ minimum radius constant : ℝ, 0 < minimum ∧ 0 < radius ∧ 0 < constant ∧
      minimum = actualParentUniformMinimum exponent lower discrepancyBound derivativeBound ∧ radius = (actualParentUniformRadius exponent lower discrepancyBound slope) ∧
      constant = actualParentFreezeTransportConstant (actualParentUniformRadius exponent lower discrepancyBound slope) (actualParentUniformRadius_positive exponent_greater_one lower_positive slope_positive).le ∧
      ∃ first second : (Bool × Bool) → ℝ → ℝ,
      parent.law = volume.withDensity (fun value => ENNReal.ofReal
        (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)) ∧
      (∑ digit : Bool × Bool, (4 : ℝ≥0∞)⁻¹ • (children digit).law) =
        volume.withDensity (fun value => ENNReal.ofReal
          (∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value)) ∧
      (∀ digit, Integrable (first digit) ∧ Integrable (second digit) ∧
        (∀ value, 0 ≤ first digit value) ∧ (∀ value, 0 ≤ second digit value) ∧
        Function.support (first digit) ⊆ Icc (-radius) radius ∧
        Function.support (second digit) ⊆ Icc (-radius) radius) ∧
      (∀ digit, Integrable (fun pair : ℝ × ℝ => |pair.1-pair.2|) (couplings digit)) ∧
      (∫ value : ℝ, |(∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (first digit) value)-
        ∑ digit : Bool × Bool, (1/4 : ℝ)*physicalAffineDensity (origins digit) width (second digit) value|) ≤
        constant*(∑ digit : Bool × Bool, (1/4 : ℝ)*
          (1+(2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)).toReal*
            (1+(fullFourierEnergy (freezing depth word) regularity).toReal+
              (fullFourierEnergy (freezing (depth+1) (Fin.snoc word digit)) regularity).toReal)))^(1/(2*(1+regularity)))*
          (12*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
            rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth)^(regularity/(1+regularity)) := by
  classical
  have power_spec := Classical.choose_spec
    (actual_selected_freezing_power_comparison lower_positive upper_positive upper_less_one square_less displacement_nonnegative)
  have powers := power_spec.2 rho root freezing rho_positive power_small prefix_displacement freezing_mem freezing_band
  have center_cost := actual_parent_center_and_cost_of_derivatives exponent_greater_one lower_positive upper_positive upper_less_one
    rho_positive normalized_nonnegative mixed_nonnegative second_nonnegative displacement_nonnegative slope_positive
    horizontalDepth verticalDepth tailDepth vertical_large root freezing prefix_displacement freezing_mem freezing_band band
    (fun depth word => (tail_comparable depth word).2) normalized_bound root_zero derivative_negative second_bound mixed_bound smallness
  have vertical_small : ∀ depth word, (freezing depth word)^verticalDepth ≤ 1/2 := by
    intro depth word
    have conditions := band depth (prefixFreshTail word (fun _ => (false, false))) (freezing depth word)
      (by simpa only [prefixFreshTail_word] using (left_mem_uIcc : freezing depth word ∈
        uIcc (freezing depth word) (root (prefixFreshTail word (fun _ => (false, false))))))
    exact conditions.2.2.2
  intro depth word
  obtain ⟨minimum, radius, constant, minimum_positive, radius_positive, constant_positive,
      minimum_eq, radius_eq, constant_eq, first, second, first_law, second_law, density_properties, integrable, estimate⟩ :=
    actual_parent_uniform_frozen_mixture_transport exponent_greater_one lower_positive discrepancy_nonnegative
      slope_positive derivative_positive rho_positive rho_small regularity_positive regularity_le_one
      horizontalDepth verticalDepth tailDepth depth word
      (fun digit => freezing (depth+1) (Fin.snoc word digit))
      (freezing_band depth word).1 ((freezing_band depth word).2.trans_lt upper_less_one)
      (fun digit => (freezing_band (depth+1) (Fin.snoc word digit)).1)
      (fun digit => (freezing_band (depth+1) (Fin.snoc word digit)).2.trans_lt upper_less_one)
      (tail_comparable depth word) (fun digit => tail_comparable (depth+1) (Fin.snoc word digit))
      (vertical_small depth word) (fun digit => vertical_small (depth+1) (Fin.snoc word digit))
      phase_bound (derivative_negative depth word) (derivative_bound depth word)
      (fun digit => derivative_negative (depth+1) (Fin.snoc word digit))
      (fun digit => derivative_bound (depth+1) (Fin.snoc word digit))
      (powers depth word) (fun digit => (center_cost depth word digit).1)
      (finite_energy depth word) (fun digit => finite_energy (depth+1) (Fin.snoc word digit))
  refine ⟨minimum, radius, constant, minimum_positive, radius_positive, constant_positive,
    minimum_eq, radius_eq, constant_eq, first, second, first_law, second_law, density_properties, integrable, ?_⟩
  apply estimate.trans
  have cost_nonnegative : 0 ≤ ∑ digit : Bool × Bool,
      ∫ pair : ℝ × ℝ, |pair.1-pair.2| ∂commonSourceCoupling First.Roots.pairedAddressMeasure
        (fun tail => (((centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)).child digit).value tail-
          ((centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)).child digit).affineCenter)/
            (rho*(freezing depth word)^depth))
        (fun tail => ((centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth (depth+1) (Fin.snoc word digit)
          (freezing (depth+1) (Fin.snoc word digit))).value tail-
            ((centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)).child digit).affineCenter)/
              (rho*(freezing depth word)^depth)) := by
    exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
  have cost_bound := Finset.sum_le_sum (fun digit (_ : digit ∈ (Finset.univ : Finset (Bool × Bool))) =>
    (center_cost depth word digit).2.2)
  have cost_bound' := cost_bound.trans_eq (show
      (∑ digit : Bool × Bool, 3*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
        rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth) =
      12*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
        rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
    ring)
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow cost_nonnegative cost_bound' (by positivity))
  apply mul_nonneg constant_positive.le
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- All numerical smallness requirements above hold simultaneously for one
large initial depth, uniformly over every later prefix depth. -/
theorem actual_parent_numerical_conditions_eventually
    {exponent center lower upper normalizedBound mixedBound secondBound displacementConstant slope : ℝ}
    (exponent_greater_one : 1 < exponent) (center_positive : 0 < center) (center_less_one : center < 1)
    (lower_positive : 0 < lower) (upper_positive : 0 < upper) (upper_less_one : upper < 1)
    (square_less : upper*upper < lower) (normalized_nonnegative : 0 ≤ normalizedBound)
    (mixed_nonnegative : 0 ≤ mixedBound) (second_nonnegative : 0 ≤ secondBound)
    (displacement_nonnegative : 0 ≤ displacementConstant) (slope_positive : 0 < slope) :
    ∀ᶠ length : ℕ in atTop, center^length ≤ 1/4 ∧
      actualSelectedPowerConstant lower_positive upper_positive upper_less_one square_less displacement_nonnegative*center^length ≤ 1/2 ∧
      ∀ depth : ℕ, 3*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
        center^length*(((length+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth ≤ 1 := by
  have exponent_positive : 0 < exponent := by linarith
  have error_nonnegative : 0 ≤ 3*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope := by
    unfold actualParentNewtonErrorConstant
    positivity
  have quotient_positive : 0 < upper^2/lower := by positivity
  have quotient_less : upper^2/lower < 1 := (div_lt_one lower_positive).mpr (by simpa only [pow_two] using square_less)
  have powers := tendsto_pow_atTop_nhds_zero_of_lt_one center_positive.le center_less_one
  have power_constant : Tendsto (fun length : ℕ =>
      actualSelectedPowerConstant lower_positive upper_positive upper_less_one square_less displacement_nonnegative*center^length)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using powers.const_mul
      (actualSelectedPowerConstant lower_positive upper_positive upper_less_one square_less displacement_nonnegative)
  have errors := uniform_newton_polynomial_geometric_smallness center_positive center_less_one
    quotient_positive quotient_less error_nonnegative (by norm_num : (0 : ℝ) < 1)
  filter_upwards [powers.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4)),
    power_constant.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)), errors]
    with length small power_small errors
  exact ⟨small.le, power_small.le, errors⟩

/-- Global actual depth mixtures, representative consistency, weighted energy
averaging and the verified freezing-series argument. The actual Fourier
average and the actual geometric family remain explicit hypotheses; no
First root-fibre dimension-mass conclusion is asserted here. -/theorem actual_freezing_L1_limit_from_selected_points
    {exponent lower upper discrepancyBound slope derivativeBound rho regularity
      normalizedBound mixedBound secondBound displacementConstant : ℝ}
    (exponent_greater_one : 1 < exponent) (lower_positive : 0 < lower)
    (upper_positive : 0 < upper) (upper_less_one : upper < 1) (square_less : upper*upper < lower)
    (discrepancy_nonnegative : 0 ≤ discrepancyBound) (slope_positive : 0 < slope)
    (derivative_positive : 0 < derivativeBound) (rho_positive : 0 < rho) (rho_small : rho ≤ 1/4)
    (regularity_positive : 0 < regularity) (regularity_le_one : regularity ≤ 1)
    (normalized_nonnegative : 0 ≤ normalizedBound) (mixed_nonnegative : 0 ≤ mixedBound)
    (second_nonnegative : 0 ≤ secondBound) (displacement_nonnegative : 0 ≤ displacementConstant)
    (power_small : actualSelectedPowerConstant lower_positive upper_positive upper_less_one square_less displacement_nonnegative*rho ≤ 1/2)
    (horizontalDepth verticalDepth tailDepth : ℕ) (vertical_large : 1 ≤ verticalDepth)
    (root : (ℕ → Bool × Bool) → ℝ) (freezing : ∀ depth, (Fin depth → Bool × Bool) → ℝ)
    (prefix_displacement : ∀ (depth : ℕ) (first second : ℕ → Bool × Bool),
      (∀ index < depth, first index = second index) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (freezing_mem : ∀ depth word, freezing depth word ∈ centeredFreezingInterval root depth displacementConstant rho upper word)
    (freezing_band : ∀ depth word, freezing depth word ∈ Icc lower upper)
    (band : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      0 < parameter ∧ parameter < 1 ∧ parameter^tailDepth ≤ 1/2 ∧ parameter^verticalDepth ≤ 1/2)
    (tail_comparable : ∀ depth word, rho/2 ≤ (freezing depth word)^tailDepth ∧ (freezing depth word)^tailDepth ≤ 2*rho)
    (phase_bound : |(verticalDepth : ℝ)-exponent*horizontalDepth| ≤ discrepancyBound)
    (normalized_bound : ∀ depth word, (verticalDepth : ℝ)^2*
      ((freezing depth word)^(-exponent*(horizontalDepth : ℝ))*((freezing depth word)^verticalDepth)^2) ≤ normalizedBound)
    (root_zero : ∀ digits, centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits (root digits) = 0)
    (derivative_negative : ∀ depth word, deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word)
      (freezing depth word) ≤ -slope)
    (derivative_bound : ∀ depth word, |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth word)
      (freezing depth word)| ≤ derivativeBound)
    (second_bound : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      |centeredNormalizedSecond exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits) parameter| ≤ secondBound)
    (mixed_bound : ∀ depth digits parameter, parameter ∈ uIcc (freezing depth (fun index => digits index)) (root digits) →
      |deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth digits) parameter-
        deriv (centeredNormalizedResidual exponent horizontalDepth verticalDepth tailDepth (pairedZeroPrefixDigits depth digits)) parameter| ≤
          mixedBound*rho*(((tailDepth+depth+1 : ℕ) : ℝ))*upper^depth)
    (finite_energy : ∀ depth word, fullFourierEnergy (freezing depth word) regularity < ⊤)
    (smallness : ∀ depth, 3*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope*
      rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth ≤ 1)
    (root_measurable : Measurable root)
    (averageConstant : ℝ) (average_nonnegative : 0 ≤ averageConstant)
    (energy_average : ∀ depth, (∑ word : Fin depth → Bool × Bool, (1/4 : ℝ)^depth*
      (1+(fullFourierEnergy (freezing depth word) regularity).toReal)) ≤
        averageConstant*upper^(-(depth : ℝ)*(1-Real.log 2/Real.log (1/lower))))
    (summability_room : (upper^2/lower)^(2*regularity) < upper^(1-Real.log 2/Real.log (1/lower))) :
    let minimum := actualParentUniformMinimum exponent lower discrepancyBound derivativeBound
    let radius := actualParentUniformRadius exponent lower discrepancyBound slope
    let constant := actualParentFreezeTransportConstant radius (actualParentUniformRadius_positive exponent_greater_one lower_positive slope_positive).le
    let coefficient := (2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)).toReal
    let amplitude := constant*((1+coefficient)*averageConstant*(1+upper^(-(1-Real.log 2/Real.log (1/lower)))))^
      (1/(2*(1+regularity)))*(12*actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope)^
        (regularity/(1+regularity))
    let kernels := fun depth word => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)
    ∃ densities : ℕ → Lp ℝ 1 volume, ∃ density : Lp ℝ 1 volume,
      (∀ depth, 0 ≤ densities depth) ∧
      (∀ depth, First.Roots.pairedAddressMeasure.map (newtonMixtureObservable depth (kernels depth)) =
        volume.withDensity (fun value => ENNReal.ofReal (densities depth value))) ∧
      Tendsto densities atTop (𝓝 density) ∧
      ‖density-densities 0‖ ≤ amplitude*rho^(regularity/(1+regularity))*
        ∑' depth : ℕ, (((tailDepth+depth+1 : ℕ) : ℝ))*freezingRatio lower upper regularity^depth ∧
      First.Roots.pairedAddressMeasure.map root = volume.withDensity (fun value => ENNReal.ofReal (density value)) := by
  classical
  dsimp only
  let minimum := actualParentUniformMinimum exponent lower discrepancyBound derivativeBound
  let radius := actualParentUniformRadius exponent lower discrepancyBound slope
  have radius_positive : 0 < radius :=
    actualParentUniformRadius_positive (discrepancyBound := discrepancyBound)
      exponent_greater_one lower_positive slope_positive
  let constant := actualParentFreezeTransportConstant radius radius_positive.le
  have constant_positive : 0 < constant := (Classical.choose_spec
    (exists_normalized_finite_mixture_transport_constant (Index := Bool × Bool) radius_positive.le)).1
  let coefficient := (2*(ENNReal.ofReal (1+(minimum^(2*regularity))⁻¹)*ENNReal.ofReal minimum⁻¹)).toReal
  have coefficient_nonnegative : 0 ≤ coefficient := ENNReal.toReal_nonneg
  let errorConstant := actualParentNewtonErrorConstant exponent normalizedBound mixedBound secondBound displacementConstant slope
  have exponent_positive : 0 < exponent := by linarith
  have error_nonnegative : 0 ≤ errorConstant := by dsimp [errorConstant, actualParentNewtonErrorConstant]; positivity
  let amplitude := constant*((1+coefficient)*averageConstant*(1+upper^(-(1-Real.log 2/Real.log (1/lower)))))^
    (1/(2*(1+regularity)))*(12*errorConstant)^(regularity/(1+regularity))
  let kernels := fun depth word => centeredFrozenNewton exponent horizontalDepth verticalDepth tailDepth depth word (freezing depth word)
  let energy := fun depth word => (fullFourierEnergy (freezing depth word) regularity).toReal
  have parents := actual_parent_uniform_increment_from_selected_points exponent_greater_one lower_positive upper_positive upper_less_one
    square_less discrepancy_nonnegative slope_positive derivative_positive rho_positive rho_small regularity_positive regularity_le_one
    normalized_nonnegative mixed_nonnegative second_nonnegative displacement_nonnegative power_small horizontalDepth verticalDepth tailDepth
    vertical_large root freezing prefix_displacement freezing_mem freezing_band band tail_comparable phase_bound normalized_bound
    root_zero derivative_negative derivative_bound second_bound mixed_bound finite_energy smallness
  choose localMinimum localRadius localConstant localMinimum_positive localRadius_positive localConstant_positive
    minimum_eq radius_eq constant_eq first second first_law second_law properties integrable estimates using parents
  let widths := fun depth word => rho*(freezing depth word)^depth
  let origins := fun depth word digit => ((kernels depth word).child digit).affineCenter
  let firstPhysical := fun depth word value => ∑ digit : Bool × Bool, (1/4 : ℝ)*
    physicalAffineDensity (origins depth word digit) (widths depth word) (first depth word digit) value
  let secondPhysical := fun depth word value => ∑ digit : Bool × Bool, (1/4 : ℝ)*
    physicalAffineDensity (origins depth word digit) (widths depth word) (second depth word digit) value
  have width_positive : ∀ depth word, 0 < widths depth word := by
    intro depth word
    dsimp [widths]
    exact mul_pos rho_positive (pow_pos (lower_positive.trans_le (freezing_band depth word).1) depth)
  have first_integrable : ∀ depth word, Integrable (firstPhysical depth word) := by
    intro depth word
    exact integrable_finset_sum _ (fun digit _ =>
      (integrable_physicalAffineDensity (properties depth word digit).1 (origins depth word digit) (width_positive depth word)).const_mul _)
  have second_integrable : ∀ depth word, Integrable (secondPhysical depth word) := by
    intro depth word
    exact integrable_finset_sum _ (fun digit _ =>
      (integrable_physicalAffineDensity (properties depth word digit).2.1 (origins depth word digit) (width_positive depth word)).const_mul _)
  have first_nonnegative : ∀ depth word, ∀ᵐ value : ℝ, 0 ≤ firstPhysical depth word value := by
    intro depth word
    exact Eventually.of_forall (fun value => Finset.sum_nonneg (fun digit _ =>
      mul_nonneg (by norm_num) (mul_nonneg (inv_nonneg.mpr (width_positive depth word).le) ((properties depth word digit).2.2.1 ((value-origins depth word digit)/widths depth word)))))
  have secondPhysical_nonnegative : ∀ depth word, ∀ᵐ value : ℝ, 0 ≤ secondPhysical depth word value := by
    intro depth word
    exact Eventually.of_forall (fun value => Finset.sum_nonneg (fun digit _ =>
      mul_nonneg (by norm_num) (mul_nonneg (inv_nonneg.mpr (width_positive depth word).le) ((properties depth word digit).2.2.2.1 ((value-origins depth word digit)/widths depth word)))))
  let majorant := fun depth word => constant*(∑ digit : Bool × Bool, (1/4 : ℝ)*
    (1+coefficient*(1+energy depth word+energy (depth+1) (Fin.snoc word digit))))^(1/(2*(1+regularity)))*
      (12*errorConstant*rho*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^2/lower)^depth)^(regularity/(1+regularity))
  have replacements : ∀ depth word,
      (∫ value : ℝ, |firstPhysical depth word value-secondPhysical depth word value|) ≤ majorant depth word := by
    intro depth word
    have bound := estimates depth word
    rw [minimum_eq depth word, constant_eq depth word] at bound
    simpa only [majorant, firstPhysical, secondPhysical, widths, origins, kernels, coefficient, minimum, constant,
      radius, energy, errorConstant] using bound
  obtain ⟨densities, nonnegative, density_laws, increments⟩ :=
    actual_depth_L1_increment_of_parent_replacements kernels firstPhysical secondPhysical majorant first_integrable second_integrable
      first_nonnegative secondPhysical_nonnegative first_law second_law replacements
  have geometric_increments : ∀ depth, ‖densities (depth+1)-densities depth‖ ≤
      amplitude*rho^(regularity/(1+regularity))*(((tailDepth+depth+1 : ℕ) : ℝ))*freezingRatio lower upper regularity^depth := by
    intro depth
    apply (increments depth).trans
    have numerical := averaged_parent_geometric_increment energy (fun _ _ => ENNReal.toReal_nonneg)
      coefficient_nonnegative average_nonnegative constant_positive.le (show 0 ≤ 12*errorConstant by positivity)
      lower_positive upper_positive regularity_positive rho_positive.le energy_average tailDepth depth
    simpa only [majorant, amplitude] using numerical
  obtain ⟨ratio_positive, ratio_less_one⟩ := freezingRatio_bounds lower_positive upper_positive regularity_positive summability_room
  obtain ⟨density, convergence, total_error⟩ := l1_kernel_limit_of_geometric_increments volume densities tailDepth 1
    (amplitude*rho^(regularity/(1+regularity))) (freezingRatio lower upper regularity) ratio_positive ratio_less_one
    (fun depth => by simpa only [pow_one, mul_assoc] using geometric_increments depth)
  have observable_error : ∀ depth digits,
      |newtonMixtureObservable depth (kernels depth) digits-root digits| ≤
        errorConstant*rho^2*(((tailDepth+depth+1 : ℕ) : ℝ))*(upper^depth)^2 := by
    intro depth digits
    have displacement := centered_freezing_root_distance root depth (prefix_displacement depth) (freezing depth) (freezing_mem depth) digits
    have slope_lower : slope ≤ |deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth
        (fun index => digits index)) (freezing depth (fun index => digits index))| := by
      have negative := derivative_negative depth (fun index => digits index)
      linarith [neg_le_abs (deriv (centeredPrefixBaseline exponent horizontalDepth verticalDepth tailDepth depth
        (fun index => digits index)) (freezing depth (fun index => digits index)))]
    have estimate := centered_actual_newton_quadratic_error exponent_greater_one horizontalDepth verticalDepth tailDepth depth digits
      rho_positive.le normalized_nonnegative mixed_nonnegative second_nonnegative (show 0 ≤ 2*displacementConstant by positivity)
      slope_positive vertical_large (band depth digits) (freezing_band depth (fun index => digits index)).2
      (tail_comparable depth (fun index => digits index)).2 (normalized_bound depth (fun index => digits index))
      (root_zero digits) slope_lower (second_bound depth digits) (mixed_bound depth digits)
      (by simpa only [mul_assoc] using displacement)
    rw [abs_sub_comm] at estimate
    simpa only [newtonMixtureObservable, kernels, errorConstant, actualParentNewtonErrorConstant] using estimate
  have pointwise := newtonMixtureObservable_tendsto_root kernels root tailDepth upper_positive upper_less_one observable_error
  have root_law := l1_limit_eq_root_law_of_same_source First.Roots.pairedAddressMeasure
    (fun depth => newtonMixtureObservable depth (kernels depth)) root
    (fun depth => newtonMixtureObservable_measurable depth (kernels depth)) root_measurable
    (Eventually.of_forall pointwise) densities density nonnegative density_laws convergence
  refine ⟨densities, density, nonnegative, density_laws, convergence, ?_, root_law⟩
  simpa only [pow_one] using total_error

end LambdaCantor.AE
