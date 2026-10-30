import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact geometry of the classical-circle cylinder in the frozen Overleaf source, Section 5.
All statements in this file are proved without additional axioms.
-/

noncomputable section
namespace LambdaCantor.Classical

def cylinderPolynomial (a b : ℝ) : ℝ :=
  (6336 + a) ^ 2 + 9 * (566 + b) ^ 2

def cylinderMap (point : ℝ × ℝ) : ℝ × ℝ :=
  ((566 + point.2) / 3 ^ 7, (6336 + point.1) / 3 ^ 8)

theorem cylinder_circle_iff (a b : ℝ) :
    ((566 + b) / 3 ^ 7) ^ 2 + ((6336 + a) / 3 ^ 8) ^ 2 = 1 ↔
      cylinderPolynomial a b = 3 ^ 16 := by
  unfold cylinderPolynomial
  constructor <;> intro h <;> norm_num at * <;> nlinarith

theorem cylinderMap_injective : Function.Injective cylinderMap := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [cylinderMap] at hx hy
  apply Prod.ext <;> norm_num at * <;> linarith

theorem cylinderMap_continuous : Continuous cylinderMap := by
  unfold cylinderMap
  fun_prop

theorem cylinder_coordinates_interior (a b : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (566 + b) / 3 ^ 7 ∈ Set.Ioo (0 : ℝ) 1 ∧
      (6336 + a) / 3 ^ 8 ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  norm_num
  constructor <;> constructor <;> linarith

theorem cylinder_corner_values :
    cylinderPolynomial 0 0 - 3 ^ 16 = -18621 ∧
      cylinderPolynomial 1 1 - 3 ^ 16 = 4249 := by
  norm_num [cylinderPolynomial]

theorem cylinder_derivative_bounds (a b : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    12672 ≤ 2 * (6336 + a) ∧ 2 * (6336 + a) ≤ 12674 ∧
      10188 ≤ 18 * (566 + b) ∧ 18 * (566 + b) ≤ 10206 := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem cylinder_ratio_bounds (a b : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (11 : ℝ) / 9 < (6336 + a) / (9 * (566 + b)) ∧
      (6336 + a) / (9 * (566 + b)) < 2027 / 1624 := by
  rcases ha with ⟨ha0, ha1⟩
  rcases hb with ⟨hb0, hb1⟩
  have hden : 0 < 9 * (566 + b) := by linarith
  constructor
  · apply (lt_div_iff₀ hden).2
    nlinarith
  · apply (div_lt_iff₀ hden).2
    nlinarith

theorem cylinder_quadratic_expansion (a b s t tailA tailB scale : ℝ)
    (hb : 566 + b ≠ 0) (hscale : scale ≠ 0) :
    (cylinderPolynomial (a + scale * (s - tailA)) (b + scale * (t - tailB)) -
        cylinderPolynomial a b) / (36 * (566 + b) * scale) =
      (((6336 + a) / (9 * (566 + b))) * s + t) / 2 -
        (((6336 + a) / (9 * (566 + b))) * tailA + tailB) / 2 +
        scale * ((s - tailA) ^ 2 + 9 * (t - tailB) ^ 2) / (36 * (566 + b)) := by
  unfold cylinderPolynomial
  field_simp
  <;> ring

theorem unit_interval_sq_difference (s t : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (s - t) ^ 2 ≤ 1 := by
  rcases hs with ⟨hs0, hs1⟩
  rcases ht with ⟨ht0, ht1⟩
  have hlow : -1 ≤ s - t := by linarith
  have hupp : s - t ≤ 1 := by linarith
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (s - t))
    (by linarith : 0 ≤ 1 + (s - t))]

theorem cylinder_remainder_bounds (b s t tailA tailB scale : ℝ)
    (hb : 0 ≤ b) (hscale : 0 ≤ scale)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha : tailA ∈ Set.Icc (0 : ℝ) 1) (hbb : tailB ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ scale * ((s - tailA) ^ 2 + 9 * (t - tailB) ^ 2) / (36 * (566 + b)) ∧
      scale * ((s - tailA) ^ 2 + 9 * (t - tailB) ^ 2) / (36 * (566 + b)) ≤
        (5 / 10188 : ℝ) * scale := by
  have hden : 0 < 36 * (566 + b) := by positivity
  have hA := unit_interval_sq_difference s tailA hs ha
  have hB := unit_interval_sq_difference t tailB ht hbb
  constructor
  · positivity
  · apply (div_le_iff₀ hden).2
    have hsum : (s - tailA) ^ 2 + 9 * (t - tailB) ^ 2 ≤ 10 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hscale
    have hsb := mul_nonneg hscale hb
    nlinarith

theorem first_child_polynomial (d e s t : ℝ) :
    9 * (cylinderPolynomial ((d + s) / 3) ((e + t) / 3) - 3 ^ 16) =
      (19008 + d + s) ^ 2 + 9 * (1698 + e + t) ^ 2 - 3 ^ 18 := by
  unfold cylinderPolynomial
  ring

theorem first_child_corner_values :
    ((19008 : ℝ)^2 + 9 * 1698^2 - 3^18 = -167589) ∧
    ((19009 : ℝ)^2 + 9 * 1699^2 - 3^18 = -98999) ∧
    ((19008 : ℝ)^2 + 9 * 1700^2 - 3^18 = -106425) ∧
    ((19009 : ℝ)^2 + 9 * 1701^2 - 3^18 = -37799) ∧
    ((19010 : ℝ)^2 + 9 * 1698^2 - 3^18 = -91553) ∧
    ((19011 : ℝ)^2 + 9 * 1699^2 - 3^18 = -22959) ∧
    ((19010 : ℝ)^2 + 9 * 1700^2 - 3^18 = -30389) ∧
    ((19011 : ℝ)^2 + 9 * 1701^2 - 3^18 = 38241) := by
  norm_num

/-! The interval exclusion step in equation (5). These hypotheses say exactly
that the tail belongs to its own child and to no other child's trimmed interior.
No conclusion about Cantor points is hidden in these algebraic hypotheses. -/

theorem isolated_zero_interval (r tail error : ℝ)
    (herr : 0 ≤ error) (hsmall : error < 1 / 3)
    (htail : 0 ≤ tail ∧ tail ≤ (r + 1) / 6)
    (hexclude : ¬ (1 / 3 + error < tail ∧ tail < 1 / 3 + (r + 1) / 6 - error)) :
    -error ≤ tail ∧ tail ≤ 1 / 3 + error := by
  constructor
  · linarith [htail.1]
  · by_contra h
    apply hexclude
    constructor <;> linarith [htail.2]

theorem isolated_one_interval (r tail error : ℝ)
    (herr : 0 ≤ error) (hsmall : error < 1 / 3) (hgap : error < (r - 1) / 3)
    (htail : 1 / 3 ≤ tail ∧ tail ≤ 1 / 3 + (r + 1) / 6)
    (hexcludeZero : ¬ (error < tail ∧ tail < (r + 1) / 6 - error))
    (hexcludeR : ¬ (r / 3 + error < tail ∧ tail < r / 3 + (r + 1) / 6 - error)) :
    (r + 1) / 6 - error ≤ tail ∧ tail ≤ r / 3 + error := by
  constructor
  · by_contra h
    apply hexcludeZero
    constructor <;> linarith [htail.1]
  · by_contra h
    apply hexcludeR
    constructor <;> linarith [htail.2]

theorem isolated_r_interval (r tail error : ℝ)
    (herr : 0 ≤ error) (hsmall : error < 1 / 3) (hgap : error < (r - 1) / 3)
    (htail : r / 3 ≤ tail ∧ tail ≤ r / 3 + (r + 1) / 6)
    (hexcludeOne : ¬ (1 / 3 + error < tail ∧ tail < 1 / 3 + (r + 1) / 6 - error))
    (hexcludeTop : ¬ ((r + 1) / 3 + error < tail ∧ tail < (r + 1) / 2 - error)) :
    (r + 3) / 6 - error ≤ tail ∧ tail ≤ (r + 1) / 3 + error := by
  constructor
  · by_contra h
    apply hexcludeOne
    constructor <;> linarith [htail.1]
  · by_contra h
    apply hexcludeTop
    constructor <;> linarith [htail.2]

theorem isolated_top_interval (r tail error : ℝ)
    (herr : 0 ≤ error) (hsmall : error < 1 / 3)
    (htail : (r + 1) / 3 ≤ tail ∧ tail ≤ (r + 1) / 2)
    (hexcludeR : ¬ (r / 3 + error < tail ∧ tail < r / 3 + (r + 1) / 6 - error)) :
    (3 * r + 1) / 6 - error ≤ tail ∧ tail ≤ (r + 1) / 2 + error := by
  constructor
  · by_contra h
    apply hexcludeR
    constructor <;> linarith [htail.1]
  · linarith [htail.2]

end LambdaCantor.Classical

