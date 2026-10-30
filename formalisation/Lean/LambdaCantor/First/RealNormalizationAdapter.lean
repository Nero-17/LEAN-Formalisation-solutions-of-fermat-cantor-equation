import LambdaCantor.First.RealNormalizationRoots
import LambdaCantor.First.RealNormalizationPrefixes

noncomputable section
namespace LambdaCantor.First.Roots

/-- Differentiation at an actual zero restores the scale removed by
normalization; the derivative-of-scale term vanishes there. -/
theorem firstRootResidual_derivative_at_zero {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hlt : ratio < 1)
    (leftDepth rightDepth padding : ℕ) (left right : ℕ → Bool)
    (hzero : realNormalizedResidual exponent leftDepth rightDepth padding left right ratio = 0) :
    deriv (firstRootResidual exponent leftDepth rightDepth padding left right) ratio =
      ratio ^ (exponent * (leftDepth : ℝ)) *
        deriv (realNormalizedResidual exponent leftDepth rightDepth padding left right) ratio := by
  have hnormalized := (differentiableAt_realNormalizedResidual hpositive hlt hexponent
    leftDepth rightDepth padding left right).hasDerivAt
  have hscale := (hasDerivAt_id ratio).rpow_const
    (p := exponent * (leftDepth : ℝ)) (Or.inl hpositive.ne')
  have hequal : firstRootResidual exponent leftDepth rightDepth padding left right =ᶠ[nhds ratio]
      (fun parameter => parameter ^ (exponent * (leftDepth : ℝ)) *
        realNormalizedResidual exponent leftDepth rightDepth padding left right parameter) := by
    filter_upwards [lt_mem_nhds hpositive] with parameter hparameter
    dsimp [realNormalizedResidual]
    field_simp [(Real.rpow_pos_of_pos hparameter (exponent * (leftDepth : ℝ))).ne']
  have hproductFunction :
      ((fun parameter : ℝ => id parameter ^ (exponent * (leftDepth : ℝ))) *
        realNormalizedResidual exponent leftDepth rightDepth padding left right) =
      (fun parameter => parameter ^ (exponent * (leftDepth : ℝ)) *
        realNormalizedResidual exponent leftDepth rightDepth padding left right parameter) := by
    funext parameter
    rfl
  have hproduct := hscale.mul hnormalized
  rw [hproductFunction] at hproduct
  rw [hequal.deriv_eq]
  simpa only [id_eq, hzero, mul_zero, zero_add] using hproduct.deriv

/-- Package actual fixed full-tail roots and the normalized derivative
bound into the concrete geometric root-fibre input. -/
theorem firstRoot_rootFibreData_of_roots {exponent lower upper : ℝ}
    (hexponent : 1 < exponent) (hlower : (1 / 4 : ℝ) < lower)
    (hupper : upper < 1 / 2) (hordered : lower < upper)
    (leftDepth rightDepth padding : ℕ) (hpad : 1 ≤ padding)
    (hrightPositive : 1 ≤ rightDepth)
    (hindex :
      (∀ left right : ℕ → Bool, ∃! ratio, ratio ∈ Set.Ioo lower upper ∧
        realNormalizedResidual exponent leftDepth rightDepth padding left right ratio = 0) ∧
      (∀ (left right : ℕ → Bool) ratio, ratio ∈ Set.Icc lower upper →
        deriv (realNormalizedResidual exponent leftDepth rightDepth padding left right) ratio ≤
          -(exponent * (1 - upper) ^ (exponent - 1) / 2))) :
    ∃ data : RootFibreData exponent, data.lower = lower ∧ data.upper = upper := by
  have hlowerPos : 0 < lower := lt_trans (by norm_num) hlower
  have hupperOne : upper < 1 := lt_trans hupper (by norm_num)
  let root : (ℕ → Bool × Bool) → ℝ := fun digits =>
    Classical.choose (hindex.1 (fun index => (digits index).1) (fun index => (digits index).2))
  have hroot (digits : ℕ → Bool × Bool) : root digits ∈ Set.Ioo lower upper ∧
      realNormalizedResidual exponent leftDepth rightDepth padding
        (fun index => (digits index).1) (fun index => (digits index).2) (root digits) = 0 :=
    (Classical.choose_spec (hindex.1 (fun index => (digits index).1) (fun index => (digits index).2))).1
  have hslope : 0 < exponent * (1 - upper) ^ (exponent - 1) / 2 :=
    div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (sub_pos.mpr hupperOne) _)) (by norm_num)
  have hequation (digits : ℕ → Bool × Bool) :
      cylinderResidual exponent (realRootLeftPrefix leftDepth) (realRootRightPrefix rightDepth)
        (leftDepth + padding) (rightDepth + padding) digits =
      firstRootResidual exponent leftDepth rightDepth padding
        (fun index => (digits index).1) (fun index => (digits index).2) := by
    funext ratio
    exact realRootPrefix_residual exponent ratio _ _ _ hpad digits
  let data : RootFibreData exponent := {
    exponent_gt_one := hexponent
    lower := lower
    upper := upper
    lower_gt_quarter := hlower
    upper_lt_half := hupper
    ordered := hordered.le
    leftWord := realRootLeftPrefix leftDepth
    rightWord := realRootRightPrefix rightDepth
    leftLength := leftDepth + padding
    rightLength := rightDepth + padding
    root := root
    root_in_band := fun digits => ⟨(hroot digits).1.1.le, (hroot digits).1.2.le⟩
    left_positive := by
      intro digits ratio hratio
      have hpos := hlowerPos.trans_le hratio.1
      have hlt := hratio.2.trans_lt hupperOne
      have haddress := address_nonnegative hpos.le hlt (fun index => (digits index).1)
      rw [realRootLeftPrefix_coordinate _ _ _ hpad]
      unfold firstRootX
      exact mul_pos (pow_pos hpos _) (add_pos_of_pos_of_nonneg (sub_pos.mpr hlt) (by positivity))
    right_positive := by
      intro digits ratio hratio
      have hpos := hlowerPos.trans_le hratio.1
      have hlt := hratio.2.trans_lt hupperOne
      have haddress := address_nonnegative hpos.le hlt (fun index => (digits index).2)
      rw [realRootRightPrefix_coordinate]
      unfold firstRootY
      exact add_pos_of_pos_of_nonneg
        (sub_pos.mpr (pow_lt_one₀ hpos.le hlt (by omega))) (by positivity)
    unique_root := by
      intro digits ratio hratio
      have hpos := hlowerPos.trans_le hratio.1
      rw [hequation]
      have hiff : firstRootResidual exponent leftDepth rightDepth padding
          (fun index => (digits index).1) (fun index => (digits index).2) ratio = 0 ↔
          realNormalizedResidual exponent leftDepth rightDepth padding
            (fun index => (digits index).1) (fun index => (digits index).2) ratio = 0 := by
        simp only [realNormalizedResidual, div_eq_zero_iff,
          (Real.rpow_pos_of_pos hpos (exponent * (leftDepth : ℝ))).ne', or_false]
      rw [hiff]
      constructor
      · intro hzero
        have hcontinuous : ContinuousOn (realNormalizedResidual exponent leftDepth
            rightDepth padding (fun index => (digits index).1)
              (fun index => (digits index).2)) (Set.Icc lower upper) := by
          intro parameter hparameter
          exact (differentiableAt_realNormalizedResidual (hlowerPos.trans_le hparameter.1)
            (hparameter.2.trans_lt hupperOne) hexponent _ _ _ _ _).continuousAt.continuousWithinAt
        apply (strictAntiOn_of_uniform_negative_derivative hcontinuous hslope
          (fun parameter hparameter => hindex.2 _ _ parameter ⟨hparameter.1.le, hparameter.2.le⟩)).injOn
          hratio ⟨(hroot digits).1.1.le, (hroot digits).1.2.le⟩
        rw [hzero, (hroot digits).2]
      · rintro rfl
        exact (hroot digits).2
    derivative_lower_bound := (exponent * (1 - upper) ^ (exponent - 1) / 2) *
      lower ^ (exponent * (leftDepth : ℝ))
    derivative_lower_bound_positive := mul_pos hslope (Real.rpow_pos_of_pos hlowerPos _)
    transverse := by
      intro digits
      have hpos := hlowerPos.trans (hroot digits).1.1
      have hlt := (hroot digits).1.2.trans hupperOne
      rw [hequation, firstRootResidual_derivative_at_zero hexponent hpos hlt _ _ _ _ _ (hroot digits).2,
        abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
      have hnegative := hindex.2 (fun index => (digits index).1) (fun index => (digits index).2)
        (root digits) ⟨(hroot digits).1.1.le, (hroot digits).1.2.le⟩
      rw [abs_of_neg ((by linarith : deriv (realNormalizedResidual exponent leftDepth rightDepth padding (fun index => (digits index).1) (fun index => (digits index).2)) (root digits) < 0))]
      have hpower := Real.rpow_le_rpow hlowerPos.le (hroot digits).1.1.le
        (show 0 ≤ exponent * (leftDepth : ℝ) by positivity)
      calc
        _ ≤ (exponent * (1 - upper) ^ (exponent - 1) / 2) *
            (root digits) ^ (exponent * (leftDepth : ℝ)) :=
          mul_le_mul_of_nonneg_left hpower hslope.le
        _ ≤ _ := by nlinarith [Real.rpow_pos_of_pos hpos (exponent * (leftDepth : ℝ))] }
  exact ⟨data, rfl, rfl⟩

/-- Every irrational exponent above one supplies concrete complete-cylinder
root-fibre data inside any prescribed band around an interior target. -/
theorem irrational_rootFibreData {exponent lower target upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hlower : (1 / 4 : ℝ) < lower) (hleft : lower < target) (hright : target < upper)
    (hupper : upper < 1 / 2) :
    ∃ data : RootFibreData exponent, data.lower = lower ∧ data.upper = upper := by
  have hexponentPos : 0 < exponent := lt_trans (by norm_num) hexponent
  have hlowerPos : 0 < lower := lt_trans (by norm_num) hlower
  have hupperOne : upper < 1 := lt_trans hupper (by norm_num)
  obtain ⟨leftDepth, rightDepth, padding, hleftDepth, hrightDepth, hpadding, hroots⟩ :=
    irrational_full_tail_roots hirrational hexponent hlowerPos hleft hright hupperOne
  obtain ⟨index, hindex, hpad, hrightPositive, hleftPositive⟩ :=
    (hroots.and ((hpadding.eventually (Filter.eventually_ge_atTop 1)).and
      ((hrightDepth.eventually (Filter.eventually_ge_atTop 1)).and
        (hleftDepth.eventually (Filter.eventually_ge_atTop 1))))).exists
  exact firstRoot_rootFibreData_of_roots hexponent hlower hupper (hleft.trans hright)
    (leftDepth index) (rightDepth index) (padding index) hpad hrightPositive hindex

end LambdaCantor.First.Roots



