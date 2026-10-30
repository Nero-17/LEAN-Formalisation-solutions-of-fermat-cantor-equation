import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

theorem transport_balancing_identities {amplitude cost regularity : ℝ}
    (hamplitude : 0 < amplitude) (hcost : 0 < cost) (hregularity : 0 < regularity) :
    amplitude * (cost ^ (1 / (1 + regularity)) /
        amplitude ^ (1 / (1 + regularity))) ^ regularity =
      amplitude ^ (1 / (1 + regularity)) * cost ^ (regularity / (1 + regularity)) ∧
    cost / (cost ^ (1 / (1 + regularity)) / amplitude ^ (1 / (1 + regularity))) =
      amplitude ^ (1 / (1 + regularity)) * cost ^ (regularity / (1 + regularity)) := by
  have hsum : 1 / (1 + regularity) + regularity / (1 + regularity) = 1 := by
    field_simp [ne_of_gt (show 0 < 1 + regularity by positivity)]
  have hproduct : 1 / (1 + regularity) * regularity = regularity / (1 + regularity) := by ring
  have hamplitude_split : amplitude ^ (1 / (1 + regularity)) *
      amplitude ^ (regularity / (1 + regularity)) = amplitude := by
    rw [← Real.rpow_add hamplitude, hsum, Real.rpow_one]
  have hcost_split : cost ^ (1 / (1 + regularity)) *
      cost ^ (regularity / (1 + regularity)) = cost := by
    rw [← Real.rpow_add hcost, hsum, Real.rpow_one]
  have hamplitude_power := (Real.rpow_pos_of_pos hamplitude (regularity / (1 + regularity))).ne'
  have hcost_power := (Real.rpow_pos_of_pos hcost (1 / (1 + regularity))).ne'
  constructor
  · rw [Real.div_rpow (Real.rpow_nonneg hcost.le _) (Real.rpow_nonneg hamplitude.le _)]
    rw [← Real.rpow_mul hcost.le, ← Real.rpow_mul hamplitude.le, hproduct]
    calc
      _ = (amplitude ^ (1 / (1 + regularity)) * amplitude ^ (regularity / (1 + regularity))) *
          (cost ^ (regularity / (1 + regularity)) / amplitude ^ (regularity / (1 + regularity))) := by
        rw [hamplitude_split]
      _ = _ := by field_simp [hamplitude_power] <;> ring
  · rw [div_div_eq_mul_div]
    apply (div_eq_iff hcost_power).mpr
    calc
      _ = (cost ^ (1 / (1 + regularity)) * cost ^ (regularity / (1 + regularity))) *
          amplitude ^ (1 / (1 + regularity)) := by rw [hcost_split]
      _ = _ := by ring

/-- The smoothing estimate gives the exact transport exponent used by the
freezing argument, including zero transport cost. -/
theorem sobolev_transport_optimization {error amplitude cost regularity firstConstant secondConstant : ℝ}
    (hamplitude : 1 ≤ amplitude) (hcost : 0 ≤ cost) (hregularity : 0 < regularity)
    (hfirst : 0 ≤ firstConstant) (hsecond : 0 ≤ secondConstant)
    (hbounded : error ≤ 2)
    (hsmoothing : ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
      error ≤ firstConstant * amplitude * scale ^ regularity + secondConstant * cost / scale) :
    error ≤ (firstConstant + secondConstant + 2) * amplitude ^ (1 / (1 + regularity)) *
      cost ^ (regularity / (1 + regularity)) := by
  have hamplitude_positive : 0 < amplitude := by linarith
  have hexponent : 0 < regularity / (1 + regularity) := by positivity
  rcases eq_or_lt_of_le hcost with hzero | hpositive
  · have hcost_zero : cost = 0 := hzero.symm
    have hlimit : Tendsto (fun scale : ℝ => firstConstant * amplitude * scale ^ regularity)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        ((tendsto_id.mono_right nhdsWithin_le_nhds :
          Tendsto (fun scale : ℝ => scale) (𝓝[>] (0 : ℝ)) (𝓝 0)).rpow_const_nhds_zero hregularity)
    have herror : error ≤ 0 := ge_of_tendsto hlimit (by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with scale hscale hscale_one
      simpa [hcost_zero] using hsmoothing scale hscale hscale_one.le)
    simpa [hcost_zero, Real.zero_rpow hexponent.ne'] using herror
  · by_cases hlarge : 1 ≤ cost
    · have hamplitude_power : 1 ≤ amplitude ^ (1 / (1 + regularity)) :=
        Real.one_le_rpow hamplitude (by positivity)
      have hcost_power : 1 ≤ cost ^ (regularity / (1 + regularity)) :=
        Real.one_le_rpow hlarge hexponent.le
      have hproduct := mul_le_mul hamplitude_power hcost_power (by norm_num) (by positivity)
      nlinarith
    · have hscale_positive : 0 < cost ^ (1 / (1 + regularity)) /
          amplitude ^ (1 / (1 + regularity)) := by positivity
      have hscale_one : cost ^ (1 / (1 + regularity)) /
          amplitude ^ (1 / (1 + regularity)) ≤ 1 := by
        apply (div_le_one (Real.rpow_pos_of_pos hamplitude_positive _)).mpr
        exact Real.rpow_le_rpow hpositive.le (by linarith) (by positivity)
      have hbound := hsmoothing _ hscale_positive hscale_one
      obtain ⟨hfirst_identity, hsecond_identity⟩ :=
        transport_balancing_identities hamplitude_positive hpositive hregularity
      have hscale_bound : error ≤ (firstConstant + secondConstant) *
          (amplitude ^ (1 / (1 + regularity)) * cost ^ (regularity / (1 + regularity))) := by
        calc
          error ≤ _ := hbound
          _ = _ := by
            rw [mul_assoc firstConstant, hfirst_identity,
              mul_div_assoc secondConstant, hsecond_identity]
            ring
      have hnonnegative : 0 ≤ amplitude ^ (1 / (1 + regularity)) *
          cost ^ (regularity / (1 + regularity)) := by positivity
      nlinarith

end LambdaCantor.AE
