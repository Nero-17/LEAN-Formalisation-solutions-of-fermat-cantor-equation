import LambdaCantor.Integer.AffineImage
import LambdaCantor.Integer.PerturbedBranching
import LambdaCantor.Integer.CountableFibres
import Mathlib.Tactic.FieldSimp

namespace LambdaCantor.Integer

def affineFibre (r level : ℝ) : Set (ℝ × ℝ) :=
  (_root_.cantorSet ×ˢ _root_.cantorSet) ∩
    {point | (r*point.1+point.2)/2=level}

noncomputable def affineChild (child : Fin 4) (point : ℝ × ℝ) : ℝ × ℝ :=
  match child.val with
  | 0 => (point.1/3, point.2/3)
  | 1 => (point.1/3, (2+point.2)/3)
  | 2 => ((2+point.1)/3, point.2/3)
  | _ => ((2+point.1)/3, (2+point.2)/3)

private theorem left_child_mem {x : ℝ} (hx : x ∈ _root_.cantorSet) :
    x/3 ∈ _root_.cantorSet := by
  rw [_root_.cantorSet_eq_union_halves]
  exact Or.inl ⟨x, hx, rfl⟩

private theorem right_child_mem {x : ℝ} (hx : x ∈ _root_.cantorSet) :
    (2+x)/3 ∈ _root_.cantorSet := by
  rw [_root_.cantorSet_eq_union_halves]
  exact Or.inr ⟨x, hx, rfl⟩

theorem affine_child_mem (child : Fin 4) (point : ℝ × ℝ)
    (member : point ∈ _root_.cantorSet ×ˢ _root_.cantorSet) :
    affineChild child point ∈ _root_.cantorSet ×ˢ _root_.cantorSet := by
  fin_cases child <;> dsimp only [affineChild]
  · exact ⟨left_child_mem member.1, left_child_mem member.2⟩
  · exact ⟨left_child_mem member.1, right_child_mem member.2⟩
  · exact ⟨right_child_mem member.1, left_child_mem member.2⟩
  · exact ⟨right_child_mem member.1, right_child_mem member.2⟩

theorem affine_child_level (r : ℝ) (child : Fin 4) (point : ℝ × ℝ) :
    (r*(affineChild child point).1+(affineChild child point).2)/2 =
      childOffset r child/3 + ((r*point.1+point.2)/2)/3 := by
  fin_cases child
  all_goals dsimp only [affineChild,childOffset]
  all_goals norm_num
  all_goals (try field_simp)
  all_goals ring

theorem affine_children_disjoint (first second : Fin 4) (different : first ≠ second)
    (p q : ℝ × ℝ) (hp : p ∈ _root_.cantorSet ×ˢ _root_.cantorSet)
    (hq : q ∈ _root_.cantorSet ×ˢ _root_.cantorSet) :
    affineChild first p ≠ affineChild second q := by
  have px := _root_.cantorSet_subset_unitInterval hp.1
  have py := _root_.cantorSet_subset_unitInterval hp.2
  have qx := _root_.cantorSet_subset_unitInterval hq.1
  have qy := _root_.cantorSet_subset_unitInterval hq.2
  intro equal
  fin_cases first <;> fin_cases second
  all_goals norm_num at different
  all_goals
    have equalFirst := congrArg Prod.fst equal
    have equalSecond := congrArg Prod.snd equal
    dsimp only [affineChild] at equalFirst equalSecond
    norm_num at equalFirst equalSecond
    linarith [px.1,px.2,py.1,py.2,qx.1,qx.2,qy.1,qy.2]

theorem affine_fibre_compact (r level : ℝ) : IsCompact (affineFibre r level) := by
  have continuous : Continuous (fun point : ℝ × ℝ => (r*point.1+point.2)/2) :=
    ((continuous_const.mul continuous_fst).add continuous_snd).div_const 2
  exact (_root_.isCompact_cantorSet.prod _root_.isCompact_cantorSet).inter_right
    (isClosed_eq continuous continuous_const)

theorem affine_fibre_extreme_countable (r : ℝ) (positive : 0 < r) :
    (affineFibre r 0).Countable ∧ (affineFibre r ((r+1)/2)).Countable := by
  constructor
  · apply (Set.countable_singleton ((0,0) : ℝ × ℝ)).mono
    intro p hp
    have px := _root_.cantorSet_subset_unitInterval hp.1.1
    have py := _root_.cantorSet_subset_unitInterval hp.1.2
    have value := hp.2
    change (r*p.1+p.2)/2=0 at value
    have productZero : r*p.1=0 := by nlinarith [mul_nonneg positive.le px.1,py.1]
    have firstZero : p.1=0 := (mul_eq_zero.mp productZero).resolve_left (ne_of_gt positive)
    apply Set.mem_singleton_iff.mpr
    exact Prod.ext firstZero (by rw [firstZero] at value; nlinarith)
  · apply (Set.countable_singleton ((1,1) : ℝ × ℝ)).mono
    intro p hp
    have px := _root_.cantorSet_subset_unitInterval hp.1.1
    have py := _root_.cantorSet_subset_unitInterval hp.1.2
    have value := hp.2
    change (r*p.1+p.2)/2=(r+1)/2 at value
    have productZero : r*(1-p.1)=0 := by
      nlinarith [mul_le_mul_of_nonneg_left px.2 positive.le,py.2]
    have firstOne : p.1=1 := by
      have differenceZero := (mul_eq_zero.mp productZero).resolve_left (ne_of_gt positive)
      linarith
    apply Set.mem_singleton_iff.mpr
    exact Prod.ext firstOne (by rw [firstOne] at value; nlinarith)

theorem uncountable_affine_level_strict (r level : ℝ) (positive : 0 < r)
    (uncountable : ¬ (affineFibre r level).Countable) :
    0 < level ∧ level < (r+1)/2 := by
  have nonempty : (affineFibre r level).Nonempty := by
    by_contra empty
    apply uncountable
    rw [Set.not_nonempty_iff_eq_empty.mp empty]
    exact Set.countable_empty
  obtain ⟨p,hp⟩ := nonempty
  have px := _root_.cantorSet_subset_unitInterval hp.1.1
  have py := _root_.cantorSet_subset_unitInterval hp.1.2
  have value := hp.2
  change (r*p.1+p.2)/2=level at value
  have closedBounds : 0 ≤ level ∧ level ≤ (r+1)/2 := by
    constructor <;> nlinarith [px.1,px.2,py.1,py.2,mul_nonneg positive.le px.1,
      mul_le_mul_of_nonneg_left px.2 positive.le]
  have notZero : level ≠ 0 := by
    intro equal
    apply uncountable
    rw [equal]
    exact (affine_fibre_extreme_countable r positive).1
  have notTop : level ≠ (r+1)/2 := by
    intro equal
    apply uncountable
    rw [equal]
    exact (affine_fibre_extreme_countable r positive).2
  exact ⟨lt_of_le_of_ne closedBounds.1 (Ne.symm notZero),
    lt_of_le_of_ne closedBounds.2 notTop⟩

theorem two_child_levels_nontrivial (r level : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (first second : Fin 4) (different : first ≠ second)
    (firstLevel : 3*level-childOffset r first ∈ Set.Icc 0 ((r+1)/2))
    (secondLevel : 3*level-childOffset r second ∈ Set.Icc 0 ((r+1)/2)) :
    (affineFibre r level).Nontrivial := by
  obtain ⟨px, hpx, py, hpy, pvalue⟩ := affine_fibre_nonempty r _ lower upper firstLevel
  obtain ⟨qx, hqx, qy, hqy, qvalue⟩ := affine_fibre_nonempty r _ lower upper secondLevel
  refine ⟨affineChild first (px,py), ?_, affineChild second (qx,qy), ?_,
    affine_children_disjoint first second different (px,py) (qx,qy) ⟨hpx,hpy⟩ ⟨hqx,hqy⟩⟩
  · refine ⟨affine_child_mem first (px,py) ⟨hpx,hpy⟩, ?_⟩
    change (r*(affineChild first (px,py)).1+(affineChild first (px,py)).2)/2=level
    rw [affine_child_level, pvalue]
    ring
  · refine ⟨affine_child_mem second (qx,qy) ⟨hqx,hqy⟩, ?_⟩
    change (r*(affineChild second (qx,qy)).1+(affineChild second (qx,qy)).2)/2=level
    rw [affine_child_level, qvalue]
    ring

theorem switch_fibre_nontrivial (r level : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (switch : level ∈ switchSet r) : (affineFibre r level).Nontrivial := by
  rcases switch_two_children r level lower upper switch with first | second | third
  · exact two_child_levels_nontrivial r level lower upper 0 1 (by decide)
      (by simpa [childOffset] using first.1) (by simpa [childOffset] using first.2)
  · exact two_child_levels_nontrivial r level lower upper 1 2 (by decide)
      (by simpa [childOffset] using second.1) (by simpa [childOffset] using second.2)
  · exact two_child_levels_nontrivial r level lower upper 2 3 (by decide)
      (by simpa [childOffset] using third.1) (by simpa [childOffset] using third.2)

/-- Switch fibres are uncountable once the digital theorem has supplied
rational coordinates for isolated points. The remaining hypothesis states
that exact analytic/digital interface explicitly. -/
theorem switch_fibre_uncountable (r level : ℝ) (lower : 1 ≤ r) (upper : r ≤ 3)
    (irrational : ∀ q : ℚ, r ≠ (q : ℝ)) (switch : level ∈ switchSet r)
    (isolated_rational : ∀ p : affineFibre r level,
      IsOpen ({p} : Set (affineFibre r level)) →
        ∃ x y : ℚ, (x : ℝ)=p.val.1 ∧ (y : ℝ)=p.val.2) :
    ¬ (affineFibre r level).Countable := by
  rcases affine_fibre_subsingleton_or_uncountable (affineFibre r level)
    (affine_fibre_compact r level) r (2*level) irrational (by
      intro p hp
      have equation := hp.2
      change (r*p.1+p.2)/2=level at equation
      linarith) isolated_rational with singleton | uncountable
  · obtain ⟨p, hp, q, hq, different⟩ := switch_fibre_nontrivial r level lower upper switch
    exact False.elim (different (singleton hp hq))
  · exact uncountable

end LambdaCantor.Integer
