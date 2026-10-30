import LambdaCantor.First.TailDecay
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open scoped NNReal
namespace LambdaCantor

theorem rpow_lipschitzOn_positive_interval (exponent : ℝ) {lower upper : ℝ}
    (hlower : 0 < lower) :
    ∃ constant : ℝ≥0, LipschitzOnWith constant (fun value : ℝ => value ^ exponent)
      (Set.Icc lower upper) := by
  have hsmooth : ContDiffOn ℝ 1 (fun value : ℝ => value ^ exponent) (Set.Icc lower upper) :=
    contDiffOn_id.rpow_const_of_ne (fun value hvalue => (lt_of_lt_of_le hlower hvalue.1).ne')
  exact hsmooth.exists_lipschitzOnWith one_ne_zero (convex_Icc lower upper) isCompact_Icc

def firstRootAmplitude (length : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  1 - ratio + ratio ^ length * address ratio digits

theorem firstRootAmplitude_mem {ratio upper : ℝ} (hratio : 0 ≤ ratio)
    (hratio_upper : ratio ≤ upper) (hupper : upper < 1) (length : ℕ) (digits : ℕ → Bool) :
    firstRootAmplitude length digits ratio ∈ Set.Icc (1 - upper) 2 := by
  have hlt : ratio < 1 := lt_of_le_of_lt hratio_upper hupper
  have hnonnegative := address_nonnegative hratio hlt digits
  have hle := address_le_one hratio hlt digits
  have hpower : ratio ^ length ≤ 1 := pow_le_one₀ hratio hlt.le
  have hpower_nonnegative := pow_nonneg hratio length
  constructor <;> dsimp [firstRootAmplitude] <;> nlinarith

/-- The leading real-power cylinder term converges uniformly as the padding
increases, simultaneously over every address and parameter in the band. -/
theorem tendstoUniformly_firstRootAmplitude_power (exponent : ℝ) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) :
    TendstoUniformly
      (fun length (point : Set.Icc lower upper × (ℕ → Bool)) =>
        firstRootAmplitude length point.2 point.1 ^ exponent)
      (fun point : Set.Icc lower upper × (ℕ → Bool) => (1 - (point.1 : ℝ)) ^ exponent)
      Filter.atTop := by
  obtain ⟨constant, hlipschitz⟩ := rpow_lipschitzOn_positive_interval exponent
    (upper := (2 : ℝ)) (sub_pos.mpr hupper)
  have hlimit := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (hlower.le.trans hordered) hupper).const_mul (constant : ℝ)
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  filter_upwards [hlimit.eventually (gt_mem_nhds (by simpa using hepsilon))] with length hlength
  intro point
  have hratio : 0 ≤ (point.1 : ℝ) := hlower.le.trans point.1.property.1
  have hlt : (point.1 : ℝ) < 1 := lt_of_le_of_lt point.1.property.2 hupper
  have hbase : 1 - (point.1 : ℝ) ∈ Set.Icc (1 - upper) 2 := by
    constructor <;> linarith [point.1.property.2]
  have hamplitude := firstRootAmplitude_mem hratio point.1.property.2 hupper length point.2
  have h := hlipschitz.dist_le_mul _ hbase _ hamplitude
  have hvalue_nonnegative := address_nonnegative hratio hlt point.2
  have hvalue_le := address_le_one hratio hlt point.2
  have htail : (point.1 : ℝ) ^ length * address point.1 point.2 ≤ upper ^ length := by
    calc
      _ ≤ (point.1 : ℝ) ^ length * 1 :=
        mul_le_mul_of_nonneg_left hvalue_le (pow_nonneg hratio length)
      _ ≤ _ := by simpa using pow_le_pow_left₀ hratio point.1.property.2 length
  have hdistance : dist (1 - (point.1 : ℝ)) (firstRootAmplitude length point.2 point.1) =
      (point.1 : ℝ) ^ length * address point.1 point.2 := by
    rw [Real.dist_eq]
    dsimp [firstRootAmplitude]
    have hnonnegative := mul_nonneg (pow_nonneg hratio length) hvalue_nonnegative
    rw [show 1 - (point.1 : ℝ) - (1 - point.1 + (point.1 : ℝ) ^ length * address point.1 point.2) =
      -((point.1 : ℝ) ^ length * address point.1 point.2) by ring,
      abs_neg, abs_of_nonneg hnonnegative]
  rw [hdistance] at h
  exact lt_of_le_of_lt (h.trans (mul_le_mul_of_nonneg_left htail constant.coe_nonneg)) hlength

/-- Uniform derivative error for the real-power leading cylinder factor. -/
theorem firstRootAmplitude_power_derivative_error (exponent : ℝ) {upper : ℝ}
    (hupper_pos : 0 < upper) (hupper : upper < 1) :
    ∃ constant : ℝ≥0, ∀ ratio ∈ Set.Ioc (0 : ℝ) upper, ∀ length digits,
      |deriv (fun parameter => firstRootAmplitude length digits parameter ^ exponent) ratio +
        exponent * (1 - ratio) ^ (exponent - 1)| ≤
      |exponent| * ((constant : ℝ) * upper ^ length + (constant + 1 : ℝ) *
        ((length : ℝ) * upper ^ (length - 1) + upper ^ length * addressParameterDerivativeBound upper)) := by
  obtain ⟨constant, hlipschitz⟩ := rpow_lipschitzOn_positive_interval (exponent - 1)
    (upper := (2 : ℝ)) (sub_pos.mpr hupper)
  refine ⟨constant, ?_⟩
  intro ratio hratio length digits
  have hlt : ratio < 1 := lt_of_le_of_lt hratio.2 hupper
  have hamplitude := firstRootAmplitude_mem hratio.1.le hratio.2 hupper length digits
  have hamplitude_pos : 0 < firstRootAmplitude length digits ratio :=
    lt_of_lt_of_le (sub_pos.mpr hupper) hamplitude.1
  have hbase : 1 - ratio ∈ Set.Icc (1 - upper) 2 := by constructor <;> linarith [hratio.1, hratio.2]
  have hone : (1 : ℝ) ∈ Set.Icc (1 - upper) 2 := by constructor <;> linarith
  have haddress_nonnegative := address_nonnegative hratio.1.le hlt digits
  have haddress_le := address_le_one hratio.1.le hlt digits
  have htail_nonnegative := mul_nonneg (pow_nonneg hratio.1.le length) haddress_nonnegative
  have htail : ratio ^ length * address ratio digits ≤ upper ^ length := by
    calc
      _ ≤ ratio ^ length * 1 := mul_le_mul_of_nonneg_left haddress_le (pow_nonneg hratio.1.le length)
      _ ≤ _ := by simpa using pow_le_pow_left₀ hratio.1.le hratio.2 length
  have hdifference : |firstRootAmplitude length digits ratio ^ (exponent - 1) -
      (1 - ratio) ^ (exponent - 1)| ≤ (constant : ℝ) * upper ^ length := by
    have h := hlipschitz.dist_le_mul _ hamplitude _ hbase
    simp only [Real.dist_eq] at h
    have heq : firstRootAmplitude length digits ratio - (1 - ratio) = ratio ^ length * address ratio digits := by
      dsimp [firstRootAmplitude]; ring
    rw [heq, abs_of_nonneg htail_nonnegative] at h
    exact h.trans (mul_le_mul_of_nonneg_left htail constant.coe_nonneg)
  have hpower_bound : |firstRootAmplitude length digits ratio ^ (exponent - 1)| ≤ constant + 1 := by
    have h := hlipschitz.dist_le_mul _ hamplitude _ hone
    have hdist : dist (firstRootAmplitude length digits ratio) 1 ≤ 1 := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hamplitude.2]
    have hbound := h.trans (mul_le_mul_of_nonneg_left hdist constant.coe_nonneg)
    simp only [Real.dist_eq, Real.one_rpow, mul_one] at hbound
    calc
      _ = |(firstRootAmplitude length digits ratio ^ (exponent - 1) - 1) + 1| := by ring_nf
      _ ≤ |firstRootAmplitude length digits ratio ^ (exponent - 1) - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ _ := by simpa only [abs_one, add_comm] using! add_le_add_right hbound (1 : ℝ)
  have htail_derivative := scaled_address_derivative_bound hratio.1 hratio.2 hupper length digits
  have htail_differentiable := (hasDerivAt_scaled_address hratio.1 hlt length digits).differentiableAt.hasDerivAt
  have hamplitude_derivative : HasDerivAt (firstRootAmplitude length digits)
      (-1 + deriv (fun parameter => parameter ^ length * address parameter digits) ratio) ratio := by
    simpa only [firstRootAmplitude, zero_sub, id_eq] using!
      (((hasDerivAt_const ratio (1 : ℝ)).sub (hasDerivAt_id ratio)).add htail_differentiable)
  rw [(hamplitude_derivative.rpow_const (p := exponent) (Or.inl hamplitude_pos.ne')).deriv]
  have heq : (-1 + deriv (fun parameter => parameter ^ length * address parameter digits) ratio) * exponent *
      firstRootAmplitude length digits ratio ^ (exponent - 1) + exponent * (1 - ratio) ^ (exponent - 1) =
      exponent * (-(firstRootAmplitude length digits ratio ^ (exponent - 1) - (1 - ratio) ^ (exponent - 1)) +
        firstRootAmplitude length digits ratio ^ (exponent - 1) *
          deriv (fun parameter => parameter ^ length * address parameter digits) ratio) := by ring
  rw [heq, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg exponent)
  calc
    _ ≤ |firstRootAmplitude length digits ratio ^ (exponent - 1) - (1 - ratio) ^ (exponent - 1)| +
        |firstRootAmplitude length digits ratio ^ (exponent - 1)| *
          |deriv (fun parameter => parameter ^ length * address parameter digits) ratio| := by
      simpa only [abs_neg, abs_mul] using abs_add_le
        (-(firstRootAmplitude length digits ratio ^ (exponent - 1) - (1 - ratio) ^ (exponent - 1)))
        (firstRootAmplitude length digits ratio ^ (exponent - 1) *
          deriv (fun parameter => parameter ^ length * address parameter digits) ratio)
    _ ≤ _ := add_le_add hdifference
      (mul_le_mul hpower_bound htail_derivative (abs_nonneg _) (by positivity))

/-- C1 convergence of the actual leading real-power cylinder term, uniformly
in both the parameter and all complete binary addresses. -/
theorem tendstoUniformly_firstRootAmplitude_power_derivative (exponent : ℝ) {lower upper : ℝ}
    (hlower : 0 < lower) (hupper : upper < 1) (hordered : lower ≤ upper) :
    TendstoUniformly
      (fun length (point : Set.Icc lower upper × (ℕ → Bool)) =>
        deriv (fun parameter => firstRootAmplitude length point.2 parameter ^ exponent) point.1)
      (fun point : Set.Icc lower upper × (ℕ → Bool) =>
        -(exponent * (1 - (point.1 : ℝ)) ^ (exponent - 1))) Filter.atTop := by
  obtain ⟨constant, hbound⟩ := firstRootAmplitude_power_derivative_error exponent
    (lt_of_lt_of_le hlower hordered) hupper
  have hpower := tendsto_pow_atTop_nhds_zero_of_lt_one (hlower.le.trans hordered) hupper
  have hderivative := tendsto_scaled_address_derivative_majorant
    (lt_of_lt_of_le hlower hordered) hupper
  have hlimit := ((hpower.const_mul (constant : ℝ)).add
    (hderivative.const_mul (constant + 1 : ℝ))).const_mul |exponent|
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  filter_upwards [hlimit.eventually (gt_mem_nhds (by simpa using hepsilon))] with length hlength
  intro point
  rw [Real.dist_eq, abs_sub_comm, sub_neg_eq_add]
  exact lt_of_le_of_lt
    (hbound point.1 ⟨lt_of_lt_of_le hlower point.1.property.1, point.1.property.2⟩ length point.2)
    hlength

end LambdaCantor



