import LambdaCantor.AE.CenteredResidualLimit

noncomputable section
open Filter
open scoped Topology
namespace LambdaCantor.AE

/-- Arbitrary varying addresses are essential here: selecting a bad
address at each depth converts failure of uniformity into one sequence
contradicting the supplied sequential limit. -/
theorem centered_eventually_uniform_lt {Address : Type*} [Nonempty Address]
    (family : ℕ → Address → ℝ → ℝ) {lower center upper width limit bound : ℝ}
    (hcenter : center ∈ Set.Icc lower upper) (hwidth : 0 ≤ width)
    (scales : ℕ → ℝ) (hscales : ∀ index, 0 ≤ scales index)
    (hscaleLimit : Tendsto scales atTop (𝓝 0)) (hbound : limit < bound)
    (hlimits : ∀ addresses : ℕ → Address, ∀ ratios : ℕ → ℝ,
      (∀ index, ratios index ∈ Set.Icc lower upper) →
      Tendsto ratios atTop (𝓝 center) →
      Tendsto (fun index => family index (addresses index) (ratios index)) atTop (𝓝 limit)) :
    ∀ᶠ index : ℕ in atTop, ∀ address ratio,
      ratio ∈ Set.Icc lower upper → |ratio - center| ≤ width * scales index →
      family index address ratio < bound := by
  classical
  have hchoices : ∀ index : ℕ, ∃ address : Address, ∃ ratio : ℝ,
      ratio ∈ Set.Icc lower upper ∧ |ratio - center| ≤ width * scales index ∧
      ((∃ address ratio, ratio ∈ Set.Icc lower upper ∧
        |ratio - center| ≤ width * scales index ∧ bound ≤ family index address ratio) →
        bound ≤ family index address ratio) := by
    intro index
    by_cases hbad : ∃ address ratio, ratio ∈ Set.Icc lower upper ∧
        |ratio - center| ≤ width * scales index ∧ bound ≤ family index address ratio
    · obtain ⟨address, ratio, hratio, hwindow, hvalue⟩ := hbad
      exact ⟨address, ratio, hratio, hwindow, fun _ => hvalue⟩
    · refine ⟨Classical.choice (inferInstance : Nonempty Address), center, hcenter, ?_, fun h => False.elim (hbad h)⟩
      simpa only [sub_self, abs_zero] using mul_nonneg hwidth (hscales index)
  choose addresses ratios hratios hwindow hbad using hchoices
  have hratioLimit : Tendsto ratios atTop (𝓝 center) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    apply squeeze_zero (fun _ => abs_nonneg _) hwindow
    simpa only [mul_zero] using hscaleLimit.const_mul width
  have hlimit := hlimits addresses ratios hratios hratioLimit
  filter_upwards [hlimit.eventually (gt_mem_nhds hbound)] with index hvalue
  intro address ratio hratio hwindow
  by_contra hnot
  exact (not_le_of_gt hvalue) (hbad index
    ⟨address, ratio, hratio, hwindow, le_of_not_gt hnot⟩)

theorem centered_eventually_uniform_abs_bound {Address : Type*} [Nonempty Address]
    (family : ℕ → Address → ℝ → ℝ) {lower center upper width limit : ℝ}
    (hcenter : center ∈ Set.Icc lower upper) (hwidth : 0 ≤ width)
    (scales : ℕ → ℝ) (hscales : ∀ index, 0 ≤ scales index)
    (hscaleLimit : Tendsto scales atTop (𝓝 0))
    (hlimits : ∀ addresses : ℕ → Address, ∀ ratios : ℕ → ℝ,
      (∀ index, ratios index ∈ Set.Icc lower upper) →
      Tendsto ratios atTop (𝓝 center) →
      Tendsto (fun index => family index (addresses index) (ratios index)) atTop (𝓝 limit)) :
    ∀ᶠ index : ℕ in atTop, ∀ address ratio,
      ratio ∈ Set.Icc lower upper → |ratio - center| ≤ width * scales index →
      |family index address ratio| ≤ |limit| + 1 := by
  have hsmall := centered_eventually_uniform_lt
    (fun index address ratio => |family index address ratio - limit|)
    hcenter hwidth scales hscales hscaleLimit (by norm_num : (0 : ℝ) < 1)
    (fun addresses ratios hratios hratioLimit => by
      simpa only [sub_self, abs_zero] using
        ((hlimits addresses ratios hratios hratioLimit).sub_const limit).abs)
  filter_upwards [hsmall] with index hsmall
  intro address ratio hratio hwindow
  calc
    |family index address ratio| = |(family index address ratio - limit) + limit| := by ring_nf
    _ ≤ |family index address ratio - limit| + |limit| := abs_add_le _ _
    _ ≤ _ := by linarith [hsmall address ratio hratio hwindow]

end LambdaCantor.AE
