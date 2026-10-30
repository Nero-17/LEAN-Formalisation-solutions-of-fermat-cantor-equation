import LambdaCantor.First.RealNormalizationFull
import LambdaCantor.First.Rotation
import LambdaCantor.First.Roots
import LambdaCantor.First.Transverse

noncomputable section
namespace LambdaCantor.First.Roots

theorem differentiableAt_realNormalizedResidual {ratio exponent : ℝ}
    (hpositive : 0 < ratio) (hlt : ratio < 1) (hexponent : 1 < exponent)
    (leftDepth rightDepth padding : ℕ) (left right : ℕ → Bool) :
    DifferentiableAt ℝ (realNormalizedResidual exponent leftDepth rightDepth padding left right) ratio := by
  exact ((hasDerivAt_firstRootResidual hpositive hlt hexponent.le
    leftDepth rightDepth padding left right).div
      ((hasDerivAt_id ratio).rpow_const (p := exponent * (leftDepth : ℝ)) (Or.inl hpositive.ne'))
      (Real.rpow_pos_of_pos hpositive _).ne').differentiableAt

/-- Actual full-tail roots from a convergent phase sequence at a positive
comparison root. -/
theorem full_tail_roots_of_phase_sequences {exponent lower target upper phase : ℝ}
    (hexponent : 1 < exponent) (hlower : 0 < lower)
    (hleft : lower < target) (hright : target < upper) (hupper : upper < 1)
    (hphase : 0 < phase) (hzero : comparison exponent phase target = 0)
    (leftDepth rightDepth : ℕ → ℕ)
    (hrightDepth : Filter.Tendsto rightDepth Filter.atTop Filter.atTop)
    (hphases : Filter.Tendsto
      (fun index => (rightDepth index : ℝ) - exponent * (leftDepth index : ℝ))
      Filter.atTop (nhds phase)) :
    ∀ᶠ index in Filter.atTop,
      (∀ left right : ℕ → Bool,
        ∃! ratio, ratio ∈ Set.Ioo lower upper ∧
          realNormalizedResidual exponent (leftDepth index) (rightDepth index) index
            left right ratio = 0) ∧
      (∀ (left right : ℕ → Bool) ratio, ratio ∈ Set.Icc lower upper →
        deriv (realNormalizedResidual exponent (leftDepth index) (rightDepth index) index
          left right) ratio ≤ -(exponent * (1 - upper) ^ (exponent - 1) / 2)) := by
  have htarget : 0 < target := hlower.trans hleft
  have htargetOne : target < 1 := hright.trans hupper
  have hlimit := tendstoUniformly_realNormalizedResidual exponent hlower hupper
    (hleft.trans hright).le hphase leftDepth rightDepth (fun index => index)
    hrightDepth Filter.tendsto_id hphases
  have hanti := comparison_strictAnti exponent
    phase
    (by linarith) hphase
  have hpositive : 0 < comparison exponent
      phase lower := by
    have h := hanti ⟨hlower, (hleft.trans hright).trans hupper⟩ ⟨htarget, htargetOne⟩ hleft
    rwa [hzero] at h
  have hnegative : comparison exponent
      phase upper < 0 := by
    have h := hanti ⟨htarget, htargetOne⟩ ⟨htarget.trans hright, hupper⟩ hright
    rwa [hzero] at h
  have hslope : 0 < exponent * (1 - upper) ^ (exponent - 1) / 2 := by
    exact div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos (sub_pos.mpr hupper) _)) (by norm_num)
  filter_upwards [Metric.tendstoUniformly_iff.mp hlimit.1 _ (half_pos hpositive),
    Metric.tendstoUniformly_iff.mp hlimit.1 _ (half_pos (neg_pos.mpr hnegative)),
    Metric.tendstoUniformly_iff.mp hlimit.2 _ hslope] with index hvalueLeft hvalueRight hderivative
  have hbound (left right : ℕ → Bool) (ratio : ℝ) (hratio : ratio ∈ Set.Icc lower upper) :
      deriv (realNormalizedResidual exponent (leftDepth index) (rightDepth index) index left right) ratio ≤
        -(exponent * (1 - upper) ^ (exponent - 1) / 2) := by
    have h := hderivative (⟨ratio, hratio⟩, (left, right))
    rw [Real.dist_eq] at h
    have herror := (abs_lt.mp h).1
    have hbase : (1 - upper) ^ (exponent - 1) ≤ (1 - ratio) ^ (exponent - 1) :=
      Real.rpow_le_rpow (sub_nonneg.mpr hupper.le) (by linarith [hratio.2]) (by linarith)
    have hphaseTerm : 0 ≤ exponent *
        (phase *
          ratio ^ (phase - 1)) :=
      mul_nonneg (by linarith) (mul_nonneg hphase.le (Real.rpow_nonneg (hlower.le.trans hratio.1) _))
    dsimp only at herror
    nlinarith
  refine ⟨?_, hbound⟩
  intro left right
  have hcontinuous : ContinuousOn
      (realNormalizedResidual exponent (leftDepth index) (rightDepth index) index left right)
      (Set.Icc lower upper) := by
    intro ratio hratio
    exact (differentiableAt_realNormalizedResidual (hlower.trans_le hratio.1)
      (hratio.2.trans_lt hupper) hexponent _ _ _ _ _).continuousAt.continuousWithinAt
  have hleftSign : 0 < realNormalizedResidual exponent (leftDepth index) (rightDepth index) index left right lower := by
    have h := hvalueLeft (⟨lower, ⟨le_rfl, (hleft.trans hright).le⟩⟩, (left, right))
    rw [Real.dist_eq] at h
    have herror := (abs_lt.mp h).2
    dsimp only at herror
    unfold comparison at hpositive herror
    linarith
  have hrightSign : realNormalizedResidual exponent (leftDepth index) (rightDepth index) index left right upper < 0 := by
    have h := hvalueRight (⟨upper, ⟨(hleft.trans hright).le, le_rfl⟩⟩, (left, right))
    rw [Real.dist_eq] at h
    have herror := (abs_lt.mp h).1
    dsimp only at herror
    unfold comparison at hnegative herror
    linarith
  exact unique_interior_root (hleft.trans hright) hcontinuous
    (strictAntiOn_of_uniform_negative_derivative hcontinuous hslope
      (fun ratio hratio => hbound left right ratio ⟨hratio.1.le, hratio.2.le⟩)) hleftSign hrightSign

/-- Irrational rotation and the actual full-tail C1 limit produce unique
roots in any prescribed interval around the selected comparison root. -/
theorem irrational_full_tail_roots {exponent lower target upper : ℝ}
    (hirrational : Irrational exponent) (hexponent : 1 < exponent)
    (hlower : 0 < lower) (hleft : lower < target) (hright : target < upper) (hupper : upper < 1) :
    ∃ leftDepth rightDepth padding : ℕ → ℕ,
      Filter.Tendsto leftDepth Filter.atTop Filter.atTop ∧
      Filter.Tendsto rightDepth Filter.atTop Filter.atTop ∧
      Filter.Tendsto padding Filter.atTop Filter.atTop ∧
      ∀ᶠ index in Filter.atTop,
        (∀ left right : ℕ → Bool,
          ∃! ratio, ratio ∈ Set.Ioo lower upper ∧
            realNormalizedResidual exponent (leftDepth index) (rightDepth index) (padding index)
              left right ratio = 0) ∧
        (∀ (left right : ℕ → Bool) ratio, ratio ∈ Set.Icc lower upper →
          deriv (realNormalizedResidual exponent (leftDepth index) (rightDepth index) (padding index)
            left right) ratio ≤ -(exponent * (1 - upper) ^ (exponent - 1) / 2)) := by
  have htarget : 0 < target := hlower.trans hleft
  have htargetOne : target < 1 := hright.trans hupper
  have hphase := chosen_phase_pos exponent target hexponent htarget htargetOne
  obtain ⟨leftDepth, rightDepth, hleftDepth, hrightDepth, hphases⟩ :=
    irrational_positive_phase_sequences hirrational hexponent hphase
  refine ⟨leftDepth, rightDepth, fun index => index, hleftDepth, hrightDepth,
    Filter.tendsto_id, ?_⟩
  exact full_tail_roots_of_phase_sequences hexponent hlower hleft hright hupper hphase
    (comparison_chosen_phase exponent target (by linarith) htarget htargetOne)
    leftDepth rightDepth hrightDepth hphases

end LambdaCantor.First.Roots
