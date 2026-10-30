import LambdaCantor.Last.PositiveDerivatives

noncomputable section
namespace LambdaCantor.Last

/-- Coordinate increment bounds implied by the derivative bounds on the square.
This form is also meaningful for functions with only one-sided boundary derivatives. -/
structure CoordinateGrowth (function : (ℝ × ℝ) → ℝ)
    (lowerS upperS lowerT upperT : ℝ) : Prop where
  horizontal : ∀ first second height : ℝ,
    first ∈ Set.Icc (0 : ℝ) 1 → second ∈ Set.Icc (0 : ℝ) 1 →
    height ∈ Set.Icc (0 : ℝ) 1 → first ≤ second →
    lowerS * (second - first) ≤ function (second, height) - function (first, height) ∧
      function (second, height) - function (first, height) ≤ upperS * (second - first)
  vertical : ∀ first second width : ℝ,
    first ∈ Set.Icc (0 : ℝ) 1 → second ∈ Set.Icc (0 : ℝ) 1 →
    width ∈ Set.Icc (0 : ℝ) 1 → first ≤ second →
    lowerT * (second - first) ≤ function (width, second) - function (width, first) ∧
      function (width, second) - function (width, first) ≤ upperT * (second - first)

namespace CoordinateGrowth
variable {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT : ℝ}

theorem affine_coordinate_mem_unit {base scale coordinate : ℝ}
    (hbase : 0 ≤ base) (hscale : 0 ≤ scale) (hupper : base + scale ≤ 1)
    (hcoordinate : coordinate ∈ Set.Icc (0 : ℝ) 1) :
    base + scale * coordinate ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> nlinarith [hcoordinate.1, hcoordinate.2]

theorem reflect (growth : CoordinateGrowth function lowerS upperS lowerT upperT) :
    CoordinateGrowth (fun point : ℝ × ℝ =>
      function (1, 1) - function (1 - point.1, 1 - point.2))
      lowerS upperS lowerT upperT := by
  have hreflection : ∀ coordinate ∈ Set.Icc (0 : ℝ) 1,
      1 - coordinate ∈ Set.Icc (0 : ℝ) 1 := by
    intro coordinate hcoordinate
    exact ⟨by linarith [hcoordinate.2], by linarith [hcoordinate.1]⟩
  constructor
  · intro first second height hfirst hsecond hheight horder
    have hbounds := growth.horizontal (1 - second) (1 - first) (1 - height)
      (hreflection second hsecond) (hreflection first hfirst)
      (hreflection height hheight) (by linarith)
    constructor <;> dsimp only <;> nlinarith [hbounds.1, hbounds.2]
  · intro first second width hfirst hsecond hwidth horder
    have hbounds := growth.vertical (1 - second) (1 - first) (1 - width)
      (hreflection second hsecond) (hreflection first hfirst)
      (hreflection width hwidth) (by linarith)
    constructor <;> dsimp only <;> nlinarith [hbounds.1, hbounds.2]

/-- Restricting to a square scales all four increment bounds by its side length. -/
theorem restrict_square (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    {baseS baseT scale : ℝ} (hbaseS : 0 ≤ baseS) (hbaseT : 0 ≤ baseT)
    (hscale : 0 ≤ scale) (hupperS : baseS + scale ≤ 1)
    (hupperT : baseT + scale ≤ 1) :
    CoordinateGrowth (fun point : ℝ × ℝ =>
      function (baseS + scale * point.1, baseT + scale * point.2))
      (scale * lowerS) (scale * upperS) (scale * lowerT) (scale * upperT) := by
  constructor
  · intro first second height hfirst hsecond hheight horder
    have hbounds := growth.horizontal (baseS + scale * first) (baseS + scale * second)
      (baseT + scale * height)
      (affine_coordinate_mem_unit hbaseS hscale hupperS hfirst)
      (affine_coordinate_mem_unit hbaseS hscale hupperS hsecond)
      (affine_coordinate_mem_unit hbaseT hscale hupperT hheight)
      (by nlinarith)
    constructor <;> dsimp only <;> nlinarith [hbounds.1, hbounds.2]
  · intro first second width hfirst hsecond hwidth horder
    have hbounds := growth.vertical (baseT + scale * first) (baseT + scale * second)
      (baseS + scale * width)
      (affine_coordinate_mem_unit hbaseT hscale hupperT hfirst)
      (affine_coordinate_mem_unit hbaseT hscale hupperT hsecond)
      (affine_coordinate_mem_unit hbaseS hscale hupperS hwidth)
      (by nlinarith)
    constructor <;> dsimp only <;> nlinarith [hbounds.1, hbounds.2]

theorem mixed_lower (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    {left right bottom top : ℝ}
    (hleft : left ∈ Set.Icc (0 : ℝ) 1) (hright : right ∈ Set.Icc (0 : ℝ) 1)
    (hbottom : bottom ∈ Set.Icc (0 : ℝ) 1) (htop : top ∈ Set.Icc (0 : ℝ) 1)
    (hhorizontal : left ≤ right) (hvertical : bottom ≤ top) :
    lowerS * (right - left) - upperT * (top - bottom) ≤
      function (right, bottom) - function (left, top) := by
  have hx := (growth.horizontal left right bottom hleft hright hbottom hhorizontal).1
  have hy := (growth.vertical bottom top left hbottom htop hleft hvertical).2
  linarith

theorem mixed_upper (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    {left right bottom top : ℝ}
    (hleft : left ∈ Set.Icc (0 : ℝ) 1) (hright : right ∈ Set.Icc (0 : ℝ) 1)
    (hbottom : bottom ∈ Set.Icc (0 : ℝ) 1) (htop : top ∈ Set.Icc (0 : ℝ) 1)
    (hhorizontal : left ≤ right) (hvertical : bottom ≤ top) :
    lowerT * (top - bottom) - upperS * (right - left) ≤
      function (left, top) - function (right, bottom) := by
  have hx := (growth.horizontal left right bottom hleft hright hbottom hhorizontal).2
  have hy := (growth.vertical bottom top left hbottom htop hleft hvertical).1
  linarith

theorem left_child_overlap (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    {ratio : ℝ} (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hstrict : (1 - 2 * ratio) * upperT < ratio * lowerS) :
    function (0, 1 - ratio) < function (ratio, ratio) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hratio_mem : ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨hratio.le, by linarith⟩
  have hone_minus : 1 - ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hbound := growth.mixed_lower hzero hratio_mem hratio_mem hone_minus hratio.le (by linarith)
  nlinarith

theorem right_child_overlap (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    {ratio : ℝ} (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hstrict : (1 - 2 * ratio) * upperT < ratio * lowerS) :
    function (1 - ratio, 1 - ratio) < function (1, ratio) := by
  have hone : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hratio_mem : ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨hratio.le, by linarith⟩
  have hone_minus : 1 - ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hbound := growth.mixed_lower hone_minus hone hratio_mem hone_minus (by linarith) (by linarith)
  nlinarith

/-- The quantitative inequality making successive lower-corner shells overlap. -/
theorem corner_shell_overlap (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    {ratio scale : ℝ} (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hscale : 0 < scale) (hscale_one : scale ≤ 1)
    (hstrict : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT) :
    function ((1 - ratio) * scale, 0) < function (ratio ^ 2 * scale, ratio * scale) := by
  have hratio_one : ratio < 1 := by linarith
  have hratio_sq : ratio ^ 2 < 1 - ratio := by nlinarith
  have hleft : ratio ^ 2 * scale ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith [mul_le_mul_of_nonneg_left hscale_one (sq_nonneg ratio)]
  have hright : (1 - ratio) * scale ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have hbottom : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have htop : ratio * scale ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have hbound := growth.mixed_upper hleft hright hbottom htop
    (mul_le_mul_of_nonneg_right hratio_sq.le hscale.le) (by positivity)
  have hstrict_scaled := mul_lt_mul_of_pos_right hstrict hscale
  nlinarith

end CoordinateGrowth

/-- An elementary four-interval fact used for all nonlinear child images. -/
theorem four_interval_double_cover {lower0 lower1 lower2 lower3 upper0 upper1 upper2 upper3 level : ℝ}
    (hlower01 : lower0 < lower1) (hlower12 : lower1 < lower2)
    (hupper01 : upper0 ≤ upper1) (hupper23 : upper2 < upper3)
    (hoverlap02 : lower2 < upper0) (hoverlap13 : lower3 < upper1)
    (hlower : lower1 < level) (hupper : level < upper2) :
    (level ∈ Set.Ioo lower0 upper0 ∧ level ∈ Set.Ioo lower1 upper1) ∨
    (level ∈ Set.Ioo lower1 upper1 ∧ level ∈ Set.Ioo lower2 upper2) ∨
    (level ∈ Set.Ioo lower2 upper2 ∧ level ∈ Set.Ioo lower3 upper3) := by
  by_cases hfirst : level ≤ lower2
  · left
    exact ⟨⟨by linarith, by linarith⟩, ⟨hlower, by linarith⟩⟩
  · by_cases hsecond : level < upper1
    · right; left
      exact ⟨⟨hlower, hsecond⟩, ⟨by linarith, hupper⟩⟩
    · right; right
      exact ⟨⟨by linarith, hupper⟩, ⟨by linarith, by linarith⟩⟩

/-- Consecutive overlapping intervals cover every level reached by a lower endpoint.
No monotonicity hypothesis is needed: the first crossing suffices. -/
theorem overlapping_shell_entry (lower upper : ℕ → ℝ) {level : ℝ}
    (hoverlap : ∀ depth, lower depth < upper (depth + 1))
    (hinitial : level < upper 0) (hcrossing : ∃ depth, lower depth < level) :
    ∃ depth, level ∈ Set.Ioo (lower depth) (upper depth) := by
  refine ⟨Nat.find hcrossing, Nat.find_spec hcrossing, ?_⟩
  cases hdepth : Nat.find hcrossing with
  | zero => simpa [hdepth] using hinitial
  | succ previous =>
      have hprevious : ¬ lower previous < level :=
        Nat.find_min hcrossing (by omega)
      have hbound := hoverlap previous
      simpa [hdepth] using (le_of_not_gt hprevious).trans_lt hbound

/-- A lower endpoint sequence tending to the corner supplies the required crossing. -/
theorem overlapping_shell_entry_of_tendsto (lower upper : ℕ → ℝ) {corner level : ℝ}
    (hlimit : Filter.Tendsto lower Filter.atTop (nhds corner))
    (hoverlap : ∀ depth, lower depth < upper (depth + 1))
    (hcorner : corner < level) (hinitial : level < upper 0) :
    ∃ depth, level ∈ Set.Ioo (lower depth) (upper depth) := by
  apply overlapping_shell_entry lower upper hoverlap hinitial
  have heventually : ∀ᶠ depth in Filter.atTop, lower depth < level :=
    hlimit.eventually (isOpen_Iio.mem_nhds hcorner)
  exact heventually.exists

/-- Lower-corner cylinders have overlapping central intervals reaching the corner. -/
theorem nonlinear_lower_corner_entry
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : ContinuousAt function (0, 0))
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hoverlap : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hlevel : function (0, 0) < level) (hupper : level < function (ratio, 1)) :
    ∃ depth : ℕ, level ∈ Set.Ioo
      (function ((1 - ratio) * ratio ^ depth, 0))
      (function (ratio * ratio ^ depth, ratio ^ depth)) := by
  have hratio_one : ratio < 1 := by linarith
  have hpower : Filter.Tendsto (fun depth : ℕ => ratio ^ depth) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio.le hratio_one
  have hpoints : Filter.Tendsto
      (fun depth : ℕ => ((1 - ratio) * ratio ^ depth, (0 : ℝ)))
      Filter.atTop (nhds (0, 0)) := by
    simpa using ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => 1 - ratio)
      Filter.atTop (nhds (1 - ratio))).mul hpower).prodMk_nhds
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  refine overlapping_shell_entry_of_tendsto
    (fun depth => function ((1 - ratio) * ratio ^ depth, 0))
    (fun depth => function (ratio * ratio ^ depth, ratio ^ depth))
    (hcontinuous.tendsto.comp hpoints) ?_ hlevel ?_
  · intro depth
    have hbound := growth.corner_shell_overlap hratio hhalf (pow_pos hratio depth)
      (pow_le_one₀ hratio.le hratio_one.le) hoverlap
    convert hbound using 1 <;> congr 1 <;> simp only [pow_succ] <;> ring
  · simpa using hupper

/-- Reflection supplies the analogous entry through upper-corner cylinders. -/
theorem nonlinear_upper_corner_entry
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuous : ContinuousAt function (1, 1))
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hoverlap : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hlower : function (1 - ratio, 0) < level) (hlevel : level < function (1, 1)) :
    ∃ depth : ℕ, level ∈ Set.Ioo
      (function (1 - ratio * ratio ^ depth, 1 - ratio ^ depth))
      (function (1 - (1 - ratio) * ratio ^ depth, 1)) := by
  have hreflection : Continuous (fun point : ℝ × ℝ => (1 - point.1, 1 - point.2)) :=
    (continuous_const.sub continuous_fst).prodMk (continuous_const.sub continuous_snd)
  have hcontinuous' : ContinuousAt
      (fun point : ℝ × ℝ => function (1, 1) - function (1 - point.1, 1 - point.2))
      (0, 0) := by
    apply continuousAt_const.sub
    have hfunctionAt : ContinuousAt function
        ((fun point : ℝ × ℝ => (1 - point.1, 1 - point.2)) (0, 0)) := by
      simpa using hcontinuous
    exact ContinuousAt.comp'
      (f := fun point : ℝ × ℝ => (1 - point.1, 1 - point.2))
      (g := function) (x := (0, 0)) hfunctionAt
      (hreflection.continuousAt (x := (0, 0)))
  obtain ⟨depth, hdepth⟩ := nonlinear_lower_corner_entry growth.reflect hcontinuous'
    hratio hhalf hoverlap
    (level := function (1, 1) - level) (by simpa using sub_pos.mpr hlevel)
    (by dsimp; simp only [sub_zero, sub_self]; linarith)
  refine ⟨depth, ?_, ?_⟩
  · dsimp at hdepth
    linarith [hdepth.2]
  · dsimp at hdepth
    simp only [sub_zero] at hdepth
    linarith [hdepth.1]

/-- Every central level belongs to two distinct first-generation corner intervals. -/
theorem nonlinear_central_double_cover
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hoverlap : (1 - 2 * ratio) * upperT < ratio * lowerS)
    (hlevel : level ∈ Set.Ioo (function (1 - ratio, 0)) (function (ratio, 1))) :
    (level ∈ Set.Ioo (function (0, 0)) (function (ratio, ratio)) ∧
      level ∈ Set.Ioo (function (1 - ratio, 0)) (function (1, ratio))) ∨
    (level ∈ Set.Ioo (function (1 - ratio, 0)) (function (1, ratio)) ∧
      level ∈ Set.Ioo (function (0, 1 - ratio)) (function (ratio, 1))) ∨
    (level ∈ Set.Ioo (function (0, 1 - ratio)) (function (ratio, 1)) ∧
      level ∈ Set.Ioo (function (1 - ratio, 1 - ratio)) (function (1, 1))) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hr : ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨hratio.le, by linarith⟩
  have hc : 1 - ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  apply four_interval_double_cover
  · have hbound := (growth.horizontal 0 (1 - ratio) 0 hzero hc hzero (by linarith)).1
    have hpositive := mul_pos hlowerS (show 0 < 1 - ratio by linarith)
    linarith
  · have hbound := growth.mixed_upper hzero hc hzero hc (by linarith) (by linarith)
    have hpositive := mul_pos (sub_pos.mpr hslope) (show 0 < 1 - ratio by linarith)
    nlinarith
  · have hbound := (growth.horizontal ratio 1 ratio hr hone hr (by linarith)).1
    have hpositive := mul_pos hlowerS (show 0 < 1 - ratio by linarith)
    linarith
  · have hbound := (growth.horizontal ratio 1 1 hr hone hone (by linarith)).1
    have hpositive := mul_pos hlowerS (show 0 < 1 - ratio by linarith)
    linarith
  · exact growth.left_child_overlap hratio hhalf hoverlap
  · exact growth.right_child_overlap hratio hhalf hoverlap
  · exact hlevel.1
  · exact hlevel.2

/-- Every strict interior level enters a central interval in an all-lower or
all-upper corner cylinder. -/
theorem nonlinear_central_entry
    {function : (ℝ × ℝ) → ℝ} {lowerS upperS lowerT upperT ratio level : ℝ}
    (growth : CoordinateGrowth function lowerS upperS lowerT upperT)
    (hcontinuousZero : ContinuousAt function (0, 0))
    (hcontinuousOne : ContinuousAt function (1, 1))
    (hratio : 0 < ratio) (hhalf : ratio < 1 / 2)
    (hlowerS : 0 < lowerS) (hslope : upperS < lowerT)
    (hoverlap : (1 - ratio - ratio ^ 2) * upperS < ratio * lowerT)
    (hlevel : level ∈ Set.Ioo (function (0, 0)) (function (1, 1))) :
    (∃ depth : ℕ, level ∈ Set.Ioo
      (function ((1 - ratio) * ratio ^ depth, 0))
      (function (ratio * ratio ^ depth, ratio ^ depth))) ∨
    (∃ depth : ℕ, level ∈ Set.Ioo
      (function (1 - ratio * ratio ^ depth, 1 - ratio ^ depth))
      (function (1 - (1 - ratio) * ratio ^ depth, 1))) := by
  by_cases hupper : level < function (ratio, 1)
  · exact Or.inl (nonlinear_lower_corner_entry growth hcontinuousZero hratio hhalf
      hoverlap hlevel.1 hupper)
  · have hzero : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have hone : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    have hr : ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨hratio.le, by linarith⟩
    have hc : 1 - ratio ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hderivative_order := growth.horizontal 0 1 0 hzero hone hzero zero_le_one
    have hupperSpositive : 0 < upperS := by
      nlinarith [hderivative_order.1, hderivative_order.2]
    have hbound := growth.mixed_upper hr hc hzero hone (by linarith) zero_le_one
    have hcentral : function (1 - ratio, 0) < function (ratio, 1) := by
      nlinarith [mul_pos hratio hupperSpositive]
    exact Or.inr (nonlinear_upper_corner_entry growth hcontinuousOne hratio hhalf
      hoverlap (hcentral.trans_le (le_of_not_gt hupper)) hlevel.2)

end LambdaCantor.Last
