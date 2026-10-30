import LambdaCantor.First.RationalPowerFourAdapter

noncomputable section
namespace LambdaCantor.First.Roots

/-- Actual full-tail powers-four cylinders supply root-fibre data arbitrarily
close to one quarter, with every root and coordinate hypothesis proved. -/
theorem powersFour_rootFibreData (phase : ℕ) (hphase : 1 ≤ phase) {upper : ℝ}
    (hupperLower : (1 / 4 : ℝ) < upper) (hupper : upper < 1 / 2) :
    ∃ data : RootFibreData ((4 ^ phase : ℕ) : ℝ), data.upper < upper := by
  let exponent : ℕ := 4 ^ phase
  have hexponent : 2 ≤ exponent := by
    have hfour : 4 ≤ (4 : ℕ) ^ phase := by
      simpa using pow_le_pow_right₀ (by norm_num : 1 ≤ (4 : ℕ)) hphase
    omega
  have hexponentReal : (1 : ℝ) < exponent := by exact_mod_cast (show 1 < exponent by omega)
  have hupperOne : upper < 1 := by linarith
  let slope : ℝ := (exponent : ℝ) * (phase : ℝ) * (1 / 4 : ℝ) ^ (phase - 1) / 2
  have hslope : 0 < slope := by
    dsimp [slope]
    have hphaseReal : (0 : ℝ) < phase := by exact_mod_cast (show 0 < phase by omega)
    positivity
  have hderivative := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_powersFourNormalizedResidual_derivative exponent phase hexponent
      (by norm_num : (0 : ℝ) < 1 / 4) hupperOne hupperLower.le)
  obtain ⟨index, hroots, hderivativeIndex⟩ :=
    ((eventually_powersFour_full_tail_unique_root phase hphase hupperLower hupper).and
      (hderivative slope hslope)).exists
  have hderivativeBound (leftDigits rightDigits : ℕ → Bool)
      (ratio : ℝ) (hratio : ratio ∈ Set.Icc (1 / 4 : ℝ) upper) :
      deriv (powersFourNormalizedResidual exponent phase index leftDigits rightDigits) ratio ≤ -slope := by
    have hbound := hderivativeIndex (⟨ratio, hratio⟩, (leftDigits, rightDigits))
    rw [Real.dist_eq] at hbound
    have herror := (abs_lt.mp hbound).1
    have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hratio.1 (phase - 1)
    have hcoefficient := mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ (exponent : ℝ) * (phase : ℝ) by positivity)
    dsimp only at herror
    dsimp [slope] at *
    nlinarith
  let root : (ℕ → Bool × Bool) → ℝ := fun digits =>
    Classical.choose (hroots (fun index => (digits index).1) (fun index => (digits index).2))
  have hroot (digits : ℕ → Bool × Bool) : root digits ∈ Set.Ioo (1 / 4 : ℝ) upper ∧
      powersFourNormalizedResidual exponent phase index
        (fun index => (digits index).1) (fun index => (digits index).2) (root digits) = 0 :=
    (Classical.choose_spec
      (hroots (fun index => (digits index).1) (fun index => (digits index).2))).1
  let residual : (ℕ → Bool × Bool) → ℝ → ℝ :=
    cylinderResidual (exponent : ℝ) (powersFourLeftPrefix index)
      (realRootRightPrefix (exponent * index + phase))
      (index + (exponent * index + phase + phase + 2))
      ((exponent * index + phase) + (exponent * index + phase + phase + 2))
  have hquotient (digits : ℕ → Bool × Bool) (ratio : ℝ) :
      powersFourNormalizedResidual exponent phase index
        (fun index => (digits index).1) (fun index => (digits index).2) ratio =
      residual digits ratio / ratio ^ (exponent * index) := by
    dsimp [residual]
    rw [powersFourPrefix_residual]
    rfl
  have hcontinuous (digits : ℕ → Bool × Bool) : ContinuousOn
      (powersFourNormalizedResidual exponent phase index
        (fun index => (digits index).1) (fun index => (digits index).2))
      (Set.Icc (1 / 4 : ℝ) upper) := by
    intro ratio hratio
    exact (differentiableAt_powersFourNormalizedResidual exponent phase index _ _
      (by linarith [hratio.1]) (hratio.2.trans_lt hupperOne)).continuousAt.continuousWithinAt
  have hanti (digits : ℕ → Bool × Bool) :=
    LambdaCantor.strictAntiOn_of_uniform_negative_derivative (hcontinuous digits) hslope
      (fun ratio hratio => hderivativeBound _ _ ratio ⟨hratio.1.le, hratio.2.le⟩)
  have hzero (digits : ℕ → Bool × Bool) (ratio : ℝ)
      (hratio : ratio ∈ Set.Icc (1 / 4 : ℝ) upper) :
      residual digits ratio = 0 ↔ ratio = root digits := by
    have hpos : 0 < ratio := by linarith [hratio.1]
    have hnormalizedZero : residual digits ratio = 0 ↔
        powersFourNormalizedResidual exponent phase index
          (fun index => (digits index).1) (fun index => (digits index).2) ratio = 0 := by
      rw [hquotient, div_eq_zero_iff]
      simp [(pow_pos hpos (exponent * index)).ne']
    rw [hnormalizedZero]
    constructor
    · intro hequal
      exact (hanti digits).injOn hratio ⟨(hroot digits).1.1.le, (hroot digits).1.2.le⟩
        (hequal.trans (hroot digits).2.symm)
    · rintro rfl
      exact (hroot digits).2
  have hderivativeScale (digits : ℕ → Bool × Bool) :
      deriv (residual digits) (root digits) =
        (root digits) ^ (exponent * index) *
          deriv (powersFourNormalizedResidual exponent phase index
            (fun index => (digits index).1) (fun index => (digits index).2)) (root digits) := by
    have hpositive : 0 < root digits := lt_trans (by norm_num) (hroot digits).1.1
    have hscale := (hasDerivAt_id (root digits)).pow (exponent * index)
    have hnormalized := (differentiableAt_powersFourNormalizedResidual exponent phase index
      (fun index => (digits index).1) (fun index => (digits index).2)
      hpositive ((hroot digits).1.2.trans hupperOne)).hasDerivAt
    have hequal : residual digits =ᶠ[nhds (root digits)]
        (fun ratio => ratio ^ (exponent * index) *
          powersFourNormalizedResidual exponent phase index
            (fun index => (digits index).1) (fun index => (digits index).2) ratio) := by
      filter_upwards [lt_mem_nhds hpositive] with ratio hratio
      rw [hquotient]
      field_simp [(pow_pos hratio (exponent * index)).ne']
    have hproductFunction :
        (id ^ (exponent * index) * powersFourNormalizedResidual exponent phase index
          (fun index => (digits index).1) (fun index => (digits index).2)) =
        (fun ratio => ratio ^ (exponent * index) *
          powersFourNormalizedResidual exponent phase index
            (fun index => (digits index).1) (fun index => (digits index).2) ratio) := by
      funext ratio
      rfl
    have hproduct := hscale.mul hnormalized
    rw [hproductFunction] at hproduct
    rw [hequal.deriv_eq]
    simpa only [Pi.pow_apply, id_eq, (hroot digits).2, mul_zero, zero_add] using hproduct.deriv
  apply rootFibreData_of_interior_roots
    (bound := slope * (1 / 4 : ℝ) ^ (exponent * index)) hexponentReal hupper
    (powersFourLeftPrefix index) (realRootRightPrefix (exponent * index + phase))
    (index + (exponent * index + phase + phase + 2))
    ((exponent * index + phase) + (exponent * index + phase + phase + 2)) root
    (fun digits => (hroot digits).1)
  · exact continuous_cylinderResidual_on_band (by positivity) (by norm_num) hupperOne
      hupperLower.le _ _ _ _
  · intro digits ratio hratio
    have hpositive : 0 < ratio := by linarith [hratio.1]
    have hlt : ratio < 1 := hratio.2.trans_lt hupperOne
    have haddress := address_nonnegative hpositive.le hlt (fun index => (digits index).1)
    rw [powersFourLeftPrefix_coordinate]
    unfold powersFourLeftFactor
    exact mul_pos (pow_pos hpositive _) (add_pos_of_pos_of_nonneg
      (sub_pos.mpr (pow_lt_one₀ hpositive.le hlt (by omega))) (by positivity))
  · intro digits ratio hratio
    have hpositive : 0 < ratio := by linarith [hratio.1]
    have hlt : ratio < 1 := hratio.2.trans_lt hupperOne
    have haddress := address_nonnegative hpositive.le hlt (fun index => (digits index).2)
    rw [realRootRightPrefix_coordinate]
    unfold firstRootY
    exact add_pos_of_pos_of_nonneg
      (sub_pos.mpr (pow_lt_one₀ hpositive.le hlt (by omega))) (by positivity)
  · exact hzero
  · exact mul_pos hslope (by positivity)
  · intro digits
    change slope * (1 / 4 : ℝ) ^ (exponent * index) ≤ |deriv (residual digits) (root digits)|
    rw [hderivativeScale, abs_mul,
      abs_of_pos (pow_pos (lt_trans (by norm_num) (hroot digits).1.1) _)]
    have hnegative := hderivativeBound (fun index => (digits index).1)
      (fun index => (digits index).2) (root digits)
      ⟨(hroot digits).1.1.le, (hroot digits).1.2.le⟩
    have hpower := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (hroot digits).1.1.le (exponent * index)
    rw [abs_of_neg (by linarith : deriv (powersFourNormalizedResidual exponent phase index
      (fun index => (digits index).1) (fun index => (digits index).2)) (root digits) < 0)]
    calc
      _ ≤ slope * (root digits) ^ (exponent * index) :=
        mul_le_mul_of_nonneg_left hpower hslope.le
      _ ≤ _ := by nlinarith [pow_pos (lt_trans (by norm_num) (hroot digits).1.1) (exponent * index)]

end LambdaCantor.First.Roots
