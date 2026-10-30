import LambdaCantor.First.RationalNormalizedResidual

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First

/-- The actual normalized two-address residual tends uniformly to
1-n*lambda^r. The depths are exactly m=nk+r and padding=m+r+2. -/
theorem tendstoUniformly_powersFourNormalizedResidual
    (exponent phase : ℕ) (hexponent : 2 ≤ exponent)
    {lower upper : ℝ} (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool))) =>
        powersFourNormalizedResidual exponent phase index point.2.1 point.2.2 point.1)
      (fun point => 1 - (exponent : ℝ) * (point.1 : ℝ) ^ phase) Filter.atTop := by
  have hpadding : Filter.Tendsto (fun index : ℕ => exponent * index + phase + phase + 2)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro index
    simp only [id_eq]
    have hmul : index ≤ exponent * index :=
      Nat.le_mul_of_pos_left index (by omega : 0 < exponent)
    omega
  have htailDepth : Filter.Tendsto
      (fun index : ℕ => phase + (exponent * index + phase + phase + 2)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro index
    simp only [id_eq]
    have hmul : index ≤ exponent * index :=
      Nat.le_mul_of_pos_left index (by omega : 0 < exponent)
    omega
  have hdepth (term : ℕ) : Filter.Tendsto
      (fun index : ℕ => (term + 1) * (exponent * index + phase) + phase) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro index
    simp only [id_eq]
    have hmul : index ≤ exponent * index :=
      Nat.le_mul_of_pos_left index (by omega : 0 < exponent)
    have hterm : exponent * index + phase ≤ (term + 1) * (exponent * index + phase) :=
      Nat.le_mul_of_pos_left (exponent * index + phase) (Nat.succ_pos term)
    omega
  have hleft := (tendstoUniformly_powersFourLeftFactor_power hlower hupper hordered
    _ hpadding exponent).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.1))
  have hscaled := tendstoUniformly_scaled_address hlower hupper hordered
  have htail : TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        (point.1 : ℝ) ^ (phase + (exponent * index + phase + phase + 2)) * address point.1 point.2)
      (fun _ => (0 : ℝ)) Filter.atTop :=
    fun entourage hentourage => htailDepth.eventually (hscaled entourage hentourage)
  have hright := (tendstoUniformly_nat_mul_zero _ htail exponent).comp
    (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have hsum := (tendstoUniformly_powersFour_binomial_remainder hlower hupper hordered exponent
    (fun term index => (term + 1) * (exponent * index + phase) + phase)
    (fun index => exponent * index + phase + phase + 2) (fun term _ => hdepth term)).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have hbase : TendstoUniformly
      (fun _ : ℕ => fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) =>
        (exponent : ℝ) * (point.1 : ℝ) ^ phase)
      (fun point => (exponent : ℝ) * (point.1 : ℝ) ^ phase) Filter.atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall (fun _ _ => by simpa only [dist_self] using hepsilon)
  have hcombined := ((hleft.sub hbase).add hright).add hsum
  simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, add_zero] at hcombined
  convert hcombined using 1
  · funext index point
    exact powersFourNormalizedResidual_decomposition exponent phase index hexponent point.2.1 point.2.2
      (ne_of_gt (hlower.trans_le point.1.property.1))
  · funext point
    simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, add_zero]

/-- Full uniform C1 convergence: the actual derivative of the normalized
residual tends to the derivative of 1-n*lambda^r, for all pairs of binary tails. -/
theorem tendstoUniformly_powersFourNormalizedResidual_derivative
    (exponent phase : ℕ) (hexponent : 2 ≤ exponent)
    {lower upper : ℝ} (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) :
    TendstoUniformly
      (fun index (point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool))) =>
        deriv (powersFourNormalizedResidual exponent phase index point.2.1 point.2.2) point.1)
      (fun point => -(exponent : ℝ) * (phase : ℝ) * (point.1 : ℝ) ^ (phase - 1)) Filter.atTop := by
  have hpadding : Filter.Tendsto (fun index : ℕ => exponent * index + phase + phase + 2)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro index
    simp only [id_eq]
    have hmul : index ≤ exponent * index :=
      Nat.le_mul_of_pos_left index (by omega : 0 < exponent)
    omega
  have htailDepth : Filter.Tendsto
      (fun index : ℕ => phase + (exponent * index + phase + phase + 2)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro index
    simp only [id_eq]
    have hmul : index ≤ exponent * index :=
      Nat.le_mul_of_pos_left index (by omega : 0 < exponent)
    omega
  have hdepth (term : ℕ) : Filter.Tendsto
      (fun index : ℕ => (term + 1) * (exponent * index + phase) + phase) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono _ Filter.tendsto_id
    intro index
    simp only [id_eq]
    have hmul : index ≤ exponent * index :=
      Nat.le_mul_of_pos_left index (by omega : 0 < exponent)
    have hterm : exponent * index + phase ≤ (term + 1) * (exponent * index + phase) :=
      Nat.le_mul_of_pos_left (exponent * index + phase) (Nat.succ_pos term)
    omega
  have hleft := (tendstoUniformly_powersFourLeftFactor_power_derivative hlower hupper hordered
    _ hpadding exponent).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.1))
  have hscaled := tendstoUniformly_scaled_address_derivative hlower hupper hordered
  have htail : TendstoUniformly
      (fun index (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter => parameter ^ (phase + (exponent * index + phase + phase + 2)) *
          address parameter point.2) point.1)
      (fun _ => (0 : ℝ)) Filter.atTop :=
    fun entourage hentourage => htailDepth.eventually (hscaled entourage hentourage)
  have hright := (tendstoUniformly_nat_mul_zero _ htail exponent).comp
    (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have hsum := (tendstoUniformly_powersFour_binomial_remainder_derivative hlower hupper hordered exponent
    (fun term index => (term + 1) * (exponent * index + phase) + phase)
    (fun index => exponent * index + phase + phase + 2) (fun term _ => hdepth term) hpadding).comp
      (fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) => (point.1, point.2.2))
  have hbase : TendstoUniformly
      (fun _ : ℕ => fun point : Set.Icc lower upper × ((ℕ → Bool) × (ℕ → Bool)) =>
        (exponent : ℝ) * (phase : ℝ) * (point.1 : ℝ) ^ (phase - 1))
      (fun point => (exponent : ℝ) * (phase : ℝ) * (point.1 : ℝ) ^ (phase - 1)) Filter.atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro epsilon hepsilon
    exact Filter.Eventually.of_forall (fun _ _ => by simpa only [dist_self] using hepsilon)
  have hcombined := ((hleft.sub hbase).add hright).add hsum
  simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, add_zero, zero_sub, ← neg_mul] at hcombined
  convert hcombined using 1
  · funext index point
    exact powersFourNormalizedResidual_derivative exponent phase index hexponent point.2.1 point.2.2
      (hlower.trans_le point.1.property.1) (point.1.property.2.trans_lt hupper)
  · funext point
    simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, add_zero, zero_sub]
    ring

end LambdaCantor.First

