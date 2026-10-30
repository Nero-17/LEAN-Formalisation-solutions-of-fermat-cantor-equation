import LambdaCantor.First.RationalNormalizationLeading

noncomputable section
open scoped BigOperators
namespace LambdaCantor.First

/-- The actual normalized residual for the two independent full binary tails
in the powers-four cylinders, with m=nk+r and padding=m+r+2. -/
def powersFourNormalizedResidual (exponent phase index : ℕ)
    (leftDigits rightDigits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  ((ratio ^ index * powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits ratio) ^ exponent +
    (1 - ratio ^ (exponent * index + phase) +
      ratio ^ ((exponent * index + phase) + (exponent * index + phase + phase + 2)) *
        address ratio rightDigits) ^ exponent - 1) / ratio ^ (exponent * index)

/-- Exact separation into the leading term, a scaled full tail, and the finite
binomial remainder. This is an identity of actual cylinder coordinates. -/
theorem powersFourNormalizedResidual_decomposition (exponent phase index : ℕ)
    (hexponent : 2 ≤ exponent) (leftDigits rightDigits : ℕ → Bool)
    {ratio : ℝ} (hratio : ratio ≠ 0) :
    powersFourNormalizedResidual exponent phase index leftDigits rightDigits ratio =
      powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits ratio ^ exponent -
        (exponent : ℝ) * ratio ^ phase +
        (exponent : ℝ) * (ratio ^ (phase + (exponent * index + phase + phase + 2)) * address ratio rightDigits) +
        ∑ term ∈ Finset.range (exponent - 1), (exponent.choose (term + 2) : ℝ) *
          (ratio ^ ((term + 1) * (exponent * index + phase) + phase) *
            (-powersFourRightFactor (exponent * index + phase + phase + 2) rightDigits ratio) ^ (term + 2)) := by
  have hidentity := powers_four_full_tail_normalization exponent index
    (exponent * index + phase) phase (exponent * index + phase + phase + 2)
    hexponent rfl ratio (address ratio leftDigits) (address ratio rightDigits) hratio
  unfold powersFourNormalizedResidual powersFourLeftFactor
  rw [hidentity]
  have hsum :
      (∑ term ∈ Finset.range (exponent - 1),
        ratio ^ ((term + 1) * (exponent * index + phase) + phase) *
          (-(1 - ratio ^ (exponent * index + phase + phase + 2) * address ratio rightDigits)) ^ (term + 2) *
            (exponent.choose (term + 2) : ℝ)) =
      ∑ term ∈ Finset.range (exponent - 1), (exponent.choose (term + 2) : ℝ) *
        (ratio ^ ((term + 1) * (exponent * index + phase) + phase) *
          (-powersFourRightFactor (exponent * index + phase + phase + 2) rightDigits ratio) ^ (term + 2)) := by
    apply Finset.sum_congr rfl
    intro term hterm
    unfold powersFourRightFactor
    ring
  rw [hsum, pow_add ratio phase (exponent * index + phase + phase + 2)]
  ring

/-- Exact derivative of the decomposed normalized residual. -/
theorem powersFourNormalizedResidual_derivative (exponent phase index : ℕ)
    (hexponent : 2 ≤ exponent) (leftDigits rightDigits : ℕ → Bool)
    {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1) :
    deriv (powersFourNormalizedResidual exponent phase index leftDigits rightDigits) ratio =
      deriv (fun parameter =>
        powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits parameter ^ exponent) ratio -
      (exponent : ℝ) * (phase : ℝ) * ratio ^ (phase - 1) +
      (exponent : ℝ) * deriv (fun parameter =>
        parameter ^ (phase + (exponent * index + phase + phase + 2)) * address parameter rightDigits) ratio +
      deriv (fun parameter => ∑ term ∈ Finset.range (exponent - 1),
        (exponent.choose (term + 2) : ℝ) *
          (parameter ^ ((term + 1) * (exponent * index + phase) + phase) *
            (-powersFourRightFactor (exponent * index + phase + phase + 2) rightDigits parameter) ^ (term + 2))) ratio := by
  have hleft := ((hasDerivAt_powersFourLeftFactor hpos hlt
    (exponent * index + phase + phase + 2) leftDigits).pow exponent).differentiableAt
  have htail := (hasDerivAt_scaled_address hpos hlt
    (phase + (exponent * index + phase + phase + 2)) rightDigits).differentiableAt
  have hsum : DifferentiableAt ℝ
      (fun parameter => ∑ term ∈ Finset.range (exponent - 1),
        (exponent.choose (term + 2) : ℝ) *
          (parameter ^ ((term + 1) * (exponent * index + phase) + phase) *
            (-powersFourRightFactor (exponent * index + phase + phase + 2) rightDigits parameter) ^ (term + 2))) ratio := by
    apply DifferentiableAt.fun_sum
    intro term hterm
    exact ((((hasDerivAt_id ratio).pow ((term + 1) * (exponent * index + phase) + phase)).mul
      (((hasDerivAt_powersFourRightFactor hpos hlt
        (exponent * index + phase + phase + 2) rightDigits).neg).pow (term + 2))).const_mul
          (exponent.choose (term + 2) : ℝ)).differentiableAt
  have hbase := ((hasDerivAt_id ratio).pow phase).const_mul (exponent : ℝ)
  have hderiv := ((hleft.hasDerivAt.sub hbase).add
    (htail.hasDerivAt.const_mul (exponent : ℝ))).add hsum.hasDerivAt
  have heventually : powersFourNormalizedResidual exponent phase index leftDigits rightDigits =ᶠ[nhds ratio]
      (fun parameter =>
        powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits parameter ^ exponent -
          (exponent : ℝ) * parameter ^ phase +
          (exponent : ℝ) * (parameter ^ (phase + (exponent * index + phase + phase + 2)) * address parameter rightDigits) +
          ∑ term ∈ Finset.range (exponent - 1), (exponent.choose (term + 2) : ℝ) *
            (parameter ^ ((term + 1) * (exponent * index + phase) + phase) *
              (-powersFourRightFactor (exponent * index + phase + phase + 2) rightDigits parameter) ^ (term + 2))) := by
    filter_upwards [lt_mem_nhds hpos] with parameter hparameter
    exact powersFourNormalizedResidual_decomposition exponent phase index hexponent
      leftDigits rightDigits (ne_of_gt hparameter)
  have hleftFunction :
      powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits ^ exponent =
        (fun parameter =>
          powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits parameter ^ exponent) := by
    funext parameter
    rfl
  rw [hleftFunction] at hderiv
  have hderivActual : HasDerivAt
      (fun parameter =>
        powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits parameter ^ exponent -
          (exponent : ℝ) * parameter ^ phase +
          (exponent : ℝ) * (parameter ^ (phase + (exponent * index + phase + phase + 2)) *
            address parameter rightDigits) +
          ∑ term ∈ Finset.range (exponent - 1), (exponent.choose (term + 2) : ℝ) *
            (parameter ^ ((term + 1) * (exponent * index + phase) + phase) *
              (-powersFourRightFactor (exponent * index + phase + phase + 2) rightDigits parameter) ^ (term + 2)))
      (deriv (fun parameter =>
        powersFourLeftFactor (exponent * index + phase + phase + 2) leftDigits parameter ^ exponent) ratio -
        (exponent : ℝ) * (phase : ℝ) * ratio ^ (phase - 1) +
        (exponent : ℝ) * deriv (fun parameter =>
          parameter ^ (phase + (exponent * index + phase + phase + 2)) * address parameter rightDigits) ratio +
        deriv (fun parameter => ∑ term ∈ Finset.range (exponent - 1),
          (exponent.choose (term + 2) : ℝ) *
            (parameter ^ ((term + 1) * (exponent * index + phase) + phase) *
              (-powersFourRightFactor (exponent * index + phase + phase + 2) rightDigits parameter) ^ (term + 2))) ratio)
      ratio := by
    convert! hderiv using 1 <;>
      (try dsimp only [Pi.pow_apply, Pi.add_apply, Pi.sub_apply, id_eq]) <;> ring
  rw [heventually.deriv_eq]
  exact hderivActual.deriv

end LambdaCantor.First

