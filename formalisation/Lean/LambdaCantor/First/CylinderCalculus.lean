import LambdaCantor.First.AddressParameter
import LambdaCantor.SelfSimilarity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

noncomputable section
namespace LambdaCantor

def firstRootX (depth padding : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  ratio ^ depth * (1 - ratio + ratio ^ padding * address ratio digits)

def firstRootY (depth padding : ℕ) (digits : ℕ → Bool) (ratio : ℝ) : ℝ :=
  1 - ratio ^ depth + ratio ^ (depth + padding) * address ratio digits

theorem hasDerivAt_firstRootX {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1)
    (depth padding : ℕ) (digits : ℕ → Bool) :
    HasDerivAt (firstRootX depth padding digits)
      ((depth : ℝ) * ratio ^ (depth - 1) *
        (1 - ratio + ratio ^ padding * address ratio digits) +
      ratio ^ depth * (-1 + (padding : ℝ) * ratio ^ (padding - 1) * address ratio digits +
        ratio ^ padding * addressParameterDerivative ratio digits)) ratio := by
  have haddress := hasDerivAt_address_parameter hpos hlt digits
  have hpower := (hasDerivAt_id ratio).pow depth
  have hpadding := (hasDerivAt_id ratio).pow padding
  convert! hpower.mul (((hasDerivAt_const ratio (1 : ℝ)).sub (hasDerivAt_id ratio)).add
    (hpadding.mul haddress)) using 1 <;> dsimp only [firstRootX, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq] <;> ring

theorem hasDerivAt_firstRootY {ratio : ℝ} (hpos : 0 < ratio) (hlt : ratio < 1)
    (depth padding : ℕ) (digits : ℕ → Bool) :
    HasDerivAt (firstRootY depth padding digits)
      (-(depth : ℝ) * ratio ^ (depth - 1) +
        ((depth + padding : ℕ) : ℝ) * ratio ^ (depth + padding - 1) * address ratio digits +
        ratio ^ (depth + padding) * addressParameterDerivative ratio digits) ratio := by
  have haddress := hasDerivAt_address_parameter hpos hlt digits
  have hpower := (hasDerivAt_id ratio).pow depth
  have hpadding := (hasDerivAt_id ratio).pow (depth + padding)
  convert! ((hasDerivAt_const ratio (1 : ℝ)).sub hpower).add
    (hpadding.mul haddress) using 1 <;> dsimp only [firstRootY, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply, id_eq] <;> ring

/-- Prefixing zeros preserves membership and multiplies the coordinate by the
corresponding power of the contraction. -/
theorem pow_mul_mem_cantorSet {ratio point : ℝ} (hnonnegative : 0 ≤ ratio)
    (hlt : ratio < 1) (hpoint : point ∈ cantorSet ratio) (depth : ℕ) :
    ratio ^ depth * point ∈ cantorSet ratio := by
  induction depth with
  | zero => simpa using hpoint
  | succ depth ih =>
    rw [cantorSet_selfsimilar hnonnegative hlt]
    left
    refine ⟨ratio ^ depth * point, ih, ?_⟩
    rw [pow_succ]
    ring

/-- The left coordinate is an actual cylinder with prefix 0^depth 1 0^padding. -/
theorem firstRootX_mem_cantorSet {ratio : ℝ} (hnonnegative : 0 ≤ ratio)
    (hlt : ratio < 1) (depth padding : ℕ) (digits : ℕ → Bool) :
    firstRootX depth (padding + 1) digits ratio ∈ cantorSet ratio := by
  apply pow_mul_mem_cantorSet hnonnegative hlt
  rw [cantorSet_selfsimilar hnonnegative hlt]
  right
  refine ⟨ratio ^ padding * address ratio digits,
    pow_mul_mem_cantorSet hnonnegative hlt ⟨digits, rfl⟩ padding, ?_⟩
  rw [pow_succ]
  ring

theorem firstRootY_mem_cantorSet {ratio : ℝ} (hnonnegative : 0 ≤ ratio)
    (hlt : ratio < 1) (depth padding : ℕ) (digits : ℕ → Bool) :
    firstRootY depth padding digits ratio ∈ cantorSet ratio := by
  have htail := pow_mul_mem_cantorSet hnonnegative hlt
    (show address ratio digits ∈ cantorSet ratio from ⟨digits, rfl⟩) padding
  have hcomplement := one_sub_mem_cantorSet hnonnegative hlt htail
  have hscaled := pow_mul_mem_cantorSet hnonnegative hlt hcomplement depth
  have hfinal := one_sub_mem_cantorSet hnonnegative hlt hscaled
  convert hfinal using 1
  dsimp [firstRootY]
  rw [pow_add]
  ring

def firstRootResidual (exponent : ℝ) (leftDepth rightDepth padding : ℕ)
    (left right : ℕ → Bool) (ratio : ℝ) : ℝ :=
  firstRootX leftDepth padding left ratio ^ exponent +
    firstRootY rightDepth padding right ratio ^ exponent - 1

theorem hasDerivAt_firstRootResidual {ratio exponent : ℝ}
    (hpos : 0 < ratio) (hlt : ratio < 1) (hexponent : 1 ≤ exponent)
    (leftDepth rightDepth padding : ℕ) (left right : ℕ → Bool) :
    HasDerivAt (firstRootResidual exponent leftDepth rightDepth padding left right)
      (deriv (firstRootX leftDepth padding left) ratio * exponent *
          firstRootX leftDepth padding left ratio ^ (exponent - 1) +
       deriv (firstRootY rightDepth padding right) ratio * exponent *
          firstRootY rightDepth padding right ratio ^ (exponent - 1)) ratio := by
  have hleft := (hasDerivAt_firstRootX hpos hlt leftDepth padding left).differentiableAt.hasDerivAt
  have hright := (hasDerivAt_firstRootY hpos hlt rightDepth padding right).differentiableAt.hasDerivAt
  exact ((hleft.rpow_const (Or.inr hexponent)).add
    (hright.rpow_const (Or.inr hexponent))).sub_const 1

end LambdaCantor




