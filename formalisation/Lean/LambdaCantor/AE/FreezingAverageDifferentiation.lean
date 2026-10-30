import LambdaCantor.AE.FreezingAverageLimit
import LambdaCantor.AE.LocallyIntegrableEnergy
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology
namespace LambdaCantor.AE

/-- Lebesgue differentiation yields a finite linear bound on all sufficiently
small centred closed-ball integrals. -/
theorem ae_eventually_closedBall_integral_bound_of_integrable
    (energy : ℝ → ℝ) (integrable : Integrable energy) :
    ∀ᵐ centre : ℝ, ∃ constant : ℝ,
      ∀ᶠ radius : ℝ in 𝓝[>] (0 : ℝ),
        (∫ point in closedBall centre radius, energy point) ≤ constant*radius := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average
    (μ := (volume : Measure ℝ)) integrable.locallyIntegrable 0] with centre differentiation
  have limit := differentiation (fun _ : ℝ => centre) (fun radius : ℝ => radius)
    (tendsto_id : Tendsto (fun radius : ℝ => radius) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)))
    (Eventually.of_forall fun _ => by simp)
  refine ⟨2*(energy centre+1), ?_⟩
  filter_upwards [limit.eventually (gt_mem_nhds (lt_add_one (energy centre))),
    self_mem_nhdsWithin] with radius average_bound radius_positive
  have mass_positive : 0 < 2*radius := mul_pos (by norm_num) radius_positive
  have average_formula :
      (⨍ point in closedBall centre radius, energy point) =
        (∫ point in closedBall centre radius, energy point)/(2*radius) := by
    rw [setAverage_eq]
    simp only [measureReal_def, Real.volume_closedBall, ENNReal.toReal_ofReal mass_positive.le,
      smul_eq_mul, div_eq_mul_inv]
    ring
  rw [average_formula] at average_bound
  have bound := ((div_lt_iff₀ mass_positive).mp average_bound).le
  nlinarith

/-- Local integrability on an open set suffices: countably many compact
truncations transfer the global differentiation estimate back to the energy. -/
theorem ae_eventually_closedBall_integral_bound_of_locallyIntegrableOn
    (energy : ℝ → ℝ) {domain : Set ℝ} (domain_open : IsOpen domain)
    (integrable : LocallyIntegrableOn energy domain volume) :
    ∀ᵐ centre : ℝ, centre ∈ domain → ∃ constant : ℝ,
      ∀ᶠ radius : ℝ in 𝓝[>] (0 : ℝ),
        (∫ point in closedBall centre radius, energy point) ≤ constant*radius := by
  classical
  have neighbourhoods : ∀ point : domain, ∃ radius : ℝ, 0 < radius ∧ closedBall point.val radius ⊆ domain := by
    intro point
    obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp (domain_open.mem_nhds point.property)
    refine ⟨radius/2, by positivity, ?_⟩
    exact (closedBall_subset_ball (by linarith)).trans contained
  choose radii radii_positive balls_inside using neighbourhoods
  have local_bound (point : domain) :
      ∀ᵐ centre : ℝ, centre ∈ ball point.val (radii point) → ∃ constant : ℝ,
        ∀ᶠ radius : ℝ in 𝓝[>] (0 : ℝ),
          (∫ position in closedBall centre radius, energy position) ≤ constant*radius := by
    have cutoff_integrable :=
      (integrable.integrableOn_compact_subset (balls_inside point) (isCompact_closedBall point.val (radii point))).integrable_indicator
        measurableSet_closedBall
    filter_upwards [ae_eventually_closedBall_integral_bound_of_integrable
      ((closedBall point.val (radii point)).indicator energy) cutoff_integrable] with centre bound
    intro centre_inside
    obtain ⟨constant, bounded⟩ := bound
    refine ⟨constant, ?_⟩
    have eventually_inside : ∀ᶠ radius : ℝ in 𝓝 (0 : ℝ),
        closedBall centre radius ⊆ closedBall point.val (radii point) :=
      (tendsto_closedBall_smallSets centre).eventually
        (Filter.eventually_smallSets.mpr
          ⟨closedBall point.val (radii point),
            mem_of_superset (isOpen_ball.mem_nhds centre_inside) ball_subset_closedBall,
            fun _ contained => contained⟩)
    filter_upwards [bounded, eventually_inside.filter_mono nhdsWithin_le_nhds] with radius bound contained
    convert bound using 1
    apply setIntegral_congr_fun measurableSet_closedBall
    intro position position_mem
    exact (indicator_of_mem (contained position_mem) energy).symm
  obtain ⟨cover, countable_cover, covers⟩ :=
    (HereditarilyLindelofSpace.isLindelof domain).elim_countable_subcover
      (fun point : domain => ball point.val (radii point)) (fun _ => isOpen_ball)
      (by intro point point_mem; exact mem_iUnion.mpr ⟨⟨point, point_mem⟩, mem_ball_self (radii_positive _)⟩)
  letI : Countable cover := countable_cover.to_subtype
  have simultaneous := ae_all_iff.mpr (fun point : cover => local_bound point.val)
  filter_upwards [simultaneous] with centre bound
  intro centre_mem
  obtain ⟨point, point_mem, ball_mem⟩ := mem_iUnion₂.mp (covers centre_mem)
  exact bound ⟨point, point_mem⟩ ball_mem

end LambdaCantor.AE

