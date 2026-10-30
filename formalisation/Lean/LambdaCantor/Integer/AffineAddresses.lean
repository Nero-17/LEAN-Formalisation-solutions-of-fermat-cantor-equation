import LambdaCantor.Integer.AffineExclusive
import LambdaCantor.Integer.GoodSlopeDomains

namespace LambdaCantor.Integer

def digitPairLabel : Bool × Bool → Fin 4
  | (false,false) => 0
  | (false,true) => 1
  | (true,false) => 2
  | (true,true) => 3

theorem digitPairLabel_injective : Function.Injective digitPairLabel := by decide +kernel

noncomputable def affineTail (r : ℝ) (first second : ℕ → Bool) (depth : ℕ) : ℝ :=
  (r*address (1/3) (fun j => first (j+depth))+
    address (1/3) (fun j => second (j+depth)))/2

private theorem address_shift_step (digits : ℕ → Bool) (depth : ℕ) :
    address (1/3) (fun j => digits (j+depth)) =
      (2/3 : ℝ)*(if digits depth then 1 else 0)+
        (1/3 : ℝ)*address (1/3) (fun j => digits (j+(depth+1))) := by
  have equation := address_first_digit (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) (fun j => digits (j+depth))
  simpa only [show (1 : ℝ)-1/3=2/3 by norm_num, Nat.zero_add,Nat.add_zero,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using equation

theorem affineTail_step (r : ℝ) (first second : ℕ → Bool) (depth : ℕ) :
    affineTail r first second (depth+1) = 3*affineTail r first second depth-
      childOffset r (digitPairLabel (first depth,second depth)) := by
  unfold affineTail
  rw [address_shift_step first depth,address_shift_step second depth]
  cases firstValue : first depth <;> cases secondValue : second depth
  all_goals simp only [firstValue,secondValue,Bool.false_eq_true,if_false,if_true,
    mul_zero,mul_one,zero_add]
  all_goals dsimp only [digitPairLabel,childOffset]
  all_goals norm_num
  all_goals (try field_simp)
  all_goals ring

theorem affineTail_bounds (r : ℝ) (positive : 0 ≤ r)
    (first second : ℕ → Bool) (depth : ℕ) :
    0 ≤ affineTail r first second depth ∧ affineTail r first second depth ≤ (r+1)/2 := by
  have firstBounds := address_nonnegative (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) (fun j => first (j+depth))
  have firstUpper := address_le_one (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) (fun j => first (j+depth))
  have secondBounds := address_nonnegative (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) (fun j => second (j+depth))
  have secondUpper := address_le_one (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1) (fun j => second (j+depth))
  unfold affineTail
  constructor <;> nlinarith [mul_nonneg positive firstBounds,
    mul_le_mul_of_nonneg_left firstUpper positive]

theorem goodSlope_between_one_three {r : ℝ} (good : GoodSlope r) : 1 < r ∧ r < 3 := by
  rcases good with h | h | h | h | h <;> constructor <;> linarith [h.1, h.2]

private theorem childOffset_encoding (r : ℝ) (digit : Fin 4) :
    childOffset r digit = ((digit.val/2 : ℕ) : ℝ)*r+((digit.val%2 : ℕ) : ℝ) := by
  fin_cases digit <;> norm_num [childOffset]

/-- The affine isolated-point rationality theorem, with the actual Cantor
addresses and a metric isolation hypothesis. It uses exact zero-error domains;
no C1 Taylor lemma is assumed here. -/
theorem isolated_affine_addresses_rational (r : ℝ) (good : GoodSlope r)
    (first second : ℕ → Bool) (radius : ℝ) (radiusPositive : 0 < radius)
    (isolated : ∀ point ∈ affineFibre r
      ((r*address (1/3) first+address (1/3) second)/2),
      dist point (address (1/3) first,address (1/3) second) < radius →
        point=(address (1/3) first,address (1/3) second)) :
    (∃ rational : ℚ, (rational : ℝ)=address (1/3) first) ∧
      (∃ rational : ℚ, (rational : ℝ)=address (1/3) second) := by
  obtain ⟨rLower,rUpper⟩ := goodSlope_between_one_three good
  obtain ⟨start,singleton⟩ := isolated_affine_eventually_singleton r first second
    radius radiusPositive isolated
  have domains : ∀ depth ≥ start,
      ((lowerCoefficient (digitPairLabel (first depth,second depth)).val).1*r+
        (lowerCoefficient (digitPairLabel (first depth,second depth)).val).2)/6 ≤
          affineTail r first second depth ∧
      affineTail r first second depth ≤
        ((upperCoefficient (digitPairLabel (first depth,second depth)).val).1*r+
        (upperCoefficient (digitPairLabel (first depth,second depth)).val).2)/6 := by
    intro depth large
    apply singleton_fibre_exclusive r _ rLower.le rUpper.le (singleton depth large)
    have bounds := affineTail_bounds r (by linarith) first second (depth+1)
    have step := affineTail_step r first second depth
    dsimp only [affineTail] at bounds step
    constructor <;> linarith [bounds.1,bounds.2]
  obtain ⟨later,periodic⟩ := good_slope_domains_eventually_periodic r good
    (fun n => digitPairLabel (first (n+start),second (n+start)))
    (fun n => affineTail r first second (n+start)) (fun _ => 0)
    (fun _ => le_rfl) (by
      intro error positive
      exact ⟨0,fun _ _ => positive⟩) (by
      intro n
      have step := affineTail_step r first second (n+start)
      rw [childOffset_encoding] at step
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,sub_add_eq_sub_sub]
        using step) (by
      intro n
      simpa only [sub_zero] using (domains (n+start) (by omega)).1) (by
      intro n
      simpa only [add_zero] using (domains (n+start) (by omega)).2)
  apply rational_addresses_of_periodic_labels digitPairLabel digitPairLabel_injective first second
  refine ⟨start+later, ?_⟩
  intro n large
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show start ≤ n by omega)
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using periodic k (by omega)

end LambdaCantor.Integer
