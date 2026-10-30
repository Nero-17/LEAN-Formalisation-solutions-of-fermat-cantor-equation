import LambdaCantor.Last.AnalyticIsolatedOpenPhases

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.Last

def ActualPhaseTolerance (ratio slope error : ℝ) : Prop :=
  error < 1 ∧ (1-2*ratio)*(1+error) < ratio*(slope-error) ∧
    (1-2*ratio)*(slope+error) < 1-error ∧ 2*error < 1-ratio ∧
    ((SmallPeriodicityPhase ratio slope ∧ 2*error < ratio-(1-2*ratio)*slope) ∨
      (MixedPeriodicityPhase ratio slope ∧ 2*error < (slope-1)*(1-ratio)))

theorem actualPhaseTolerance_near_zero {ratio slope : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope) :
    ∀ᶠ error : ℝ in 𝓝 0, ActualPhaseTolerance ratio slope error := by
  have weak := periodicity_phase_weak_overlaps above_third less_half phase
  have complement_positive : (0 : ℝ) < 1-ratio := by linarith
  have first : ∀ᶠ error : ℝ in 𝓝 0, error < 1 := gt_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have outer : ∀ᶠ error : ℝ in 𝓝 0,
      (1-2*ratio)*(1+error) < ratio*(slope-error) :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using weak.2.1)
  have middle : ∀ᶠ error : ℝ in 𝓝 0,
      (1-2*ratio)*(slope+error) < 1-error :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using weak.2.2)
  have exterior : ∀ᶠ error : ℝ in 𝓝 0, 2*error < 1-ratio :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using complement_positive)
  rcases phase with small | mixed
  · have cover_positive : (0 : ℝ) < ratio-(1-2*ratio)*slope := sub_pos.mpr small.2.1
    have mixed_cover : ∀ᶠ error : ℝ in 𝓝 0, 2*error < ratio-(1-2*ratio)*slope :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds (by simpa using cover_positive)
    filter_upwards [first, outer, middle, exterior, mixed_cover] with error hfirst houter hmiddle hexterior hcover
    exact ⟨hfirst, houter, hmiddle, hexterior, Or.inl ⟨small, hcover⟩⟩
  · have order_positive : (0 : ℝ) < (slope-1)*(1-ratio) :=
      mul_pos (sub_pos.mpr mixed.1) complement_positive
    have ordered : ∀ᶠ error : ℝ in 𝓝 0, 2*error < (slope-1)*(1-ratio) :=
      (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds
        (by simpa using order_positive)
    filter_upwards [first, outer, middle, exterior, ordered] with error hfirst houter hmiddle hexterior hordered
    exact ⟨hfirst, houter, hmiddle, hexterior, Or.inr ⟨mixed, hordered⟩⟩

theorem eventually_actualPhaseTolerance {ratio slope coefficient : ℝ}
    (above_third : (1/3 : ℝ) < ratio) (less_half : ratio < 1/2)
    (phase : SmallPeriodicityPhase ratio slope ∨ MixedPeriodicityPhase ratio slope) :
    ∃ cutoff : ℕ, ∀ depth, cutoff ≤ depth →
      ActualPhaseTolerance ratio slope (coefficient*ratio^depth) := by
  have positive : 0 ≤ ratio := by linarith
  have less_one : ratio < 1 := by linarith
  have errors_zero : Tendsto (fun depth : ℕ => coefficient*ratio^depth) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one positive less_one))
  exact Filter.eventually_atTop.mp
    (errors_zero.eventually (actualPhaseTolerance_near_zero above_third less_half phase))

end LambdaCantor.Last
