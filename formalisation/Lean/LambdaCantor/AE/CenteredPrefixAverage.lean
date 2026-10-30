import LambdaCantor.AE.CenteredPrefixFreezing
import LambdaCantor.AE.FreezingAverageLocal

noncomputable section
open Set MeasureTheory
namespace LambdaCantor.AE

def centeredFreezingInterval (root : (ℕ → Bool × Bool) → ℝ) (depth : ℕ)
    (displacementConstant rho upper : ℝ) (word : Fin depth → Bool × Bool) : Set ℝ :=
  Icc (root (centeredPrefixRepresentative depth word)-displacementConstant*rho*upper^depth)
    (root (centeredPrefixRepresentative depth word)+displacementConstant*rho*upper^depth)

/-- Choose actual freezing points and obtain the manuscript's averaged energy
bound from the actual root-law estimates and a local energy average. -/
theorem centered_freezing_average
    (root : (ℕ → Bool × Bool) → ℝ) (root_measurable : Measurable root) (depth : ℕ)
    {centre rho upper dimension displacementConstant smallBallConstant windowConstant averageConstant : ℝ}
    (rho_positive : 0 < rho) (upper_positive : 0 < upper) (upper_less_one : upper < 1)
    (displacement_positive : 0 < displacementConstant) (smallBall_nonnegative : 0 ≤ smallBallConstant)
    (roots_window : ∀ digits, |root digits-centre| ≤ windowConstant*rho)
    (prefix_displacement : ∀ first second : ℕ → Bool × Bool,
      (∀ position < depth, first position = second position) →
      |root first-root second| ≤ displacementConstant*rho*upper^depth)
    (small_ball : ∀ left right : ℝ, left ≤ right →
      First.Roots.rootLaw root (Icc left right) ≤ ENNReal.ofReal (smallBallConstant*((right-left)/rho)^dimension))
    (energy : ℝ → ℝ)
    (integrable : IntegrableOn energy
      (Icc (centre-(windowConstant+displacementConstant)*rho) (centre+(windowConstant+displacementConstant)*rho)))
    (nonnegative : ∀ point, 0 ≤ energy point)
    (local_average : (∫ point in
      Icc (centre-(windowConstant+displacementConstant)*rho) (centre+(windowConstant+displacementConstant)*rho),
      energy point) ≤ averageConstant*rho) :
    ∃ freezing : (Fin depth → Bool × Bool) → ℝ,
      (∀ word, freezing word ∈ centeredFreezingInterval root depth displacementConstant rho upper word) ∧
      (∑ word, (1/4:ℝ)^depth * energy (freezing word)) ≤
        (2*(smallBallConstant*(4*displacementConstant)^dimension)*averageConstant/(2*displacementConstant)) *
          upper^(-(depth:ℝ)*(1-dimension)) := by
  classical
  have radius_positive : 0 < displacementConstant*rho*upper^depth := by positivity
  have radius_bound : displacementConstant*rho*upper^depth ≤ displacementConstant*rho := by
    have power_bound := pow_le_one₀ upper_positive.le upper_less_one.le (n := depth)
    simpa using mul_le_mul_of_nonneg_left power_bound (mul_nonneg displacement_positive.le rho_positive.le)
  have contained : ∀ word, centeredFreezingInterval root depth displacementConstant rho upper word ⊆
      Icc (centre-(windowConstant+displacementConstant)*rho) (centre+(windowConstant+displacementConstant)*rho) := by
    intro word point point_mem
    have root_bounds := abs_le.mp (roots_window (centeredPrefixRepresentative depth word))
    change point ∈ Icc _ _ at point_mem
    constructor <;> nlinarith [point_mem.1, point_mem.2, root_bounds.1, root_bounds.2]
  have freezing_exists : ∀ word : Fin depth → Bool × Bool, ∃ point ∈
      centeredFreezingInterval root depth displacementConstant rho upper word,
      energy point ≤ 2/(2*displacementConstant*rho*upper^depth) *
        ∫ parameter in centeredFreezingInterval root depth displacementConstant rho upper word, energy parameter := by
    intro word
    obtain ⟨point, point_mem, average⟩ := exists_freezing_point_le_average energy
      (show root (centeredPrefixRepresentative depth word)-displacementConstant*rho*upper^depth <
        root (centeredPrefixRepresentative depth word)+displacementConstant*rho*upper^depth by linarith)
      (integrable.mono_set (contained word))
    refine ⟨point, point_mem, average.trans ?_⟩
    have length_identity :
        (root (centeredPrefixRepresentative depth word)+displacementConstant*rho*upper^depth) -
        (root (centeredPrefixRepresentative depth word)-displacementConstant*rho*upper^depth) =
        2*displacementConstant*rho*upper^depth := by ring
    rw [length_identity]
    have integral_nonnegative : 0 ≤ ∫ parameter in centeredFreezingInterval root depth displacementConstant rho upper word,
        energy parameter := integral_nonneg nonnegative
    apply mul_le_mul_of_nonneg_right _ integral_nonnegative
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  choose freezing freezing_mem freezing_bound using freezing_exists
  refine ⟨freezing, freezing_mem, ?_⟩
  have overlap := centered_root_freezing_overlap root root_measurable depth rho_positive upper_positive
    displacement_positive smallBall_nonnegative prefix_displacement small_ball
  have weighted := weighted_freezing_energy_bound_local
    (Icc (centre-(windowConstant+displacementConstant)*rho) (centre+(windowConstant+displacementConstant)*rho))
    measurableSet_Icc (centeredFreezingInterval root depth displacementConstant rho upper)
    (fun _ => measurableSet_Icc) contained (fun _ => (1/4:ℝ)^depth) (fun _ => by positivity)
    energy integrable (fun point _ => nonnegative point) freezing freezing_mem (by positivity)
    freezing_bound overlap
  exact freezing_depth_bound depth (by positivity) rho_positive upper_positive (by positivity)
    local_average weighted

end LambdaCantor.AE
