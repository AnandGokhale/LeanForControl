import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL
import LeanForControl.Analysis.DiniDeriv
import LeanForControl.ODEs.ComparisonLemma
import LeanForControl.ODEs.ODE_properties
import LeanForControl.ODEs.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic
import Architect


/-!
# `Stability.ClassKDecay`

Class KL bound from the scalar decay ODE `ẏ = -α(y)` with `α ∈ ClassK`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Appendix C.

## Main results

* `ClassK.exists_classKL_decaySolution` — the decay ODE `ẏ = −α(y)` has a class KL solution
  operator, for `α` at most linear near the origin.
* `classK_dini_bound` — a continuous `v` with `D⁺v ≤ −α(v)` is bounded by that solution.

Only these two are public. Everything else in this file is the construction behind them.

## The construction (private)

Write `η(y) = -∫_{base}^y dx/α(x)` for the time the solution started at `base` takes to reach
`y`. Because `α > 0` on `(0,a)`, `η` is continuous and strictly decreasing there; and because
`α(x) ≤ Lx` near `0`, `η(y) ≥ (log base − log y)/L → +∞` as `y → 0⁺`, so the origin is never
reached in finite time. Then `σ(r, s) = η⁻¹(η(r) + s)`, extended by `σ(0, s) = 0`, is the
solution operator: advancing time by `s` moves `η` up by `s` and so moves the state down.

`η` and `η⁻¹` are steps in building a solution, not facts about class K functions, so they are
`private` — the two results above are the whole interface.

Reference for the construction: Osgood's condition; see Khalil, Appendix C.
-/

open Set Filter Topology MeasureTheory intervalIntegral

/-- Adding a constant is an isometry, so it preserves a Lipschitz bound.  Mathlib has no
`LipschitzWith.add_const`, and the perturbed field `-β + λ` needs one. -/
private lemma lipschitzWith_add_const {L : NNReal} {f : ℝ → ℝ}
    (h : LipschitzWith L f) (c : ℝ) : LipschitzWith L (fun x => f x + c) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Real.dist_eq, add_sub_add_right_eq_sub] using h.dist_le_mul x y

private lemma ClassK.pos_on_Ioo (α : ClassK a b) {x : ℝ} (hx : x ∈ Ioo 0 a) :
    0 < α.toFun x :=
  (α.pos_iff ⟨hx.1.le, hx.2⟩).mpr hx.1


section OsgoodConstruction

variable {a b : ℝ}

/-! ### Definitions -/

/-- The *time-to-go* integral: `η_base(y) = −∫_{base}^y 1/α(x) dx`.
    Strictly decreasing on `(0, a)` because `α > 0` makes the integrand positive. -/
private noncomputable def ClassK.eta (α : ClassK a b) (base y : ℝ) : ℝ :=
  -∫ x in base..y, (1 / α.toFun x)

/-- The Osgood condition: `η_base(y) → +∞` as `y → 0⁺`.
    This ensures the system `ẏ = −α(y)` never reaches the origin in finite time. -/
private def ClassK.EtaDiverges (α : ClassK a b) (base : ℝ) : Prop :=
  Filter.Tendsto (α.eta base) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop

open Classical in
/-- The partial inverse of η: `etaInv base t` is the unique `r ∈ (0, a)` with `η(r) = t`,
    or `0` if no such `r` exists (outside the range of η). -/
private noncomputable def ClassK.etaInv (α : ClassK a b) (base : ℝ) : ℝ → ℝ :=
  fun t => if h : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t
           then Classical.choose h
           else 0

/-- The Class KL candidate: `σ(r, s) = η⁻¹(η(r) + s)`, extended by `σ(0, s) = 0`
    to avoid the singularity of η at the origin. -/
private noncomputable def ClassK.sigma (α : ClassK a b) (base r s : ℝ) : ℝ :=
  if r = 0 then 0 else α.etaInv base (α.eta base r + s)

/-! ### Properties of η -/

/-- **FTC:** the derivative of `η_base` at `y ∈ (0, a)` is `−1/α(y)`.
    Requires `1/α` to be interval-integrable and strongly measurable near `y`,
    both of which follow from continuity of `1/α` on `(0, a)`. -/
private lemma eta_hasDerivAt (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a)
    {y : ℝ} (hy : y ∈ Ioo 0 a) :
    HasDerivAt (α.eta base) (-1 / α.toFun y) y := by
  have hcont_inv : ContinuousOn (fun x => 1 / α.toFun x) (Ioo 0 a) :=
    continuousOn_const.div (α.continuous.mono Ioo_subset_Ico_self)
      (fun x hx => (α.pos_on_Ioo hx).ne')
  have hf_cont : ContinuousAt (fun x => 1 / α.toFun x) y :=
    hcont_inv.continuousAt (Ioo_mem_nhds hy.1 hy.2)
  have hf_intble : IntervalIntegrable (fun x => 1 / α.toFun x) volume base y := by
    apply (hcont_inv.mono _).intervalIntegrable
    intro x hx
    -- hx : x ∈ uIcc base y = Icc (min base y) (max base y)
    -- so hx.1 : min base y ≤ x,  hx.2 : x ≤ max base y
    exact ⟨lt_of_lt_of_le (lt_min hbase.1 hy.1) hx.1,
      lt_of_le_of_lt hx.2 (max_lt hbase.2 hy.2)⟩
  have hmeas : StronglyMeasurableAtFilter (fun x => 1 / α.toFun x) (𝓝 y) volume :=
    ⟨Ioo 0 a, Ioo_mem_nhds hy.1 hy.2, hcont_inv.aestronglyMeasurable measurableSet_Ioo⟩
  -- FTC: d/dy ∫_base^y f = f(y)
  have hderiv : HasDerivAt (fun u => ∫ x in base..u, 1 / α.toFun x) (1 / α.toFun y) y :=
    integral_hasDerivAt_right hf_intble hmeas hf_cont
  change HasDerivAt (fun u => -(∫ x in base..u, 1 / α.toFun x)) (-1 / α.toFun y) y
  -- Negate: η is minus the primitive, so its derivative is `-(1/α(y))`.
  have hderiv_neg := hderiv.neg
  simp only at hderiv_neg
  convert hderiv_neg using 1
  ring

/-- η is strictly anti-monotone on `(0, a)`: `α > 0` implies `η' = −1/α < 0` throughout. -/
private lemma eta_strictAntiOn (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a) :
    StrictAntiOn (α.eta base) (Ioo 0 a) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 a)
  · -- ContinuousOn: each point has a HasDerivAt, hence is continuous
    exact fun y hy =>
      (eta_hasDerivAt α base hbase hy).continuousAt.continuousWithinAt
  · -- deriv < 0 on the interior (= Ioo 0 a itself)
    intro x hx
    rw [interior_Ioo] at hx
    rw [(eta_hasDerivAt α base hbase hx).deriv]
    exact div_neg_of_neg_of_pos (by norm_num) (α.pos_on_Ioo hx)

/-- η is continuous on `(0, a)` (differentiability at each point implies continuity). -/
private lemma eta_continuousOn (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a) :
    ContinuousOn (α.eta base) (Ioo 0 a) := fun _ hy =>
  (eta_hasDerivAt α base hbase hy).continuousAt.continuousWithinAt

/-- For `r ∈ (0, a)` and `s ≥ 0`, the value `η(r) + s` lies in the range of η on `(0, a)`.
    `EtaDiverges` supplies `ε` near 0 with `η(ε) ≥ η(r) + s`; IVT on `[ε, r]` gives the witness. -/
private lemma eta_add_mem_range (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base)
    {r : ℝ} (hr : r ∈ Ioo 0 a) {s : ℝ} (hs : 0 ≤ s) :
    ∃ r' ∈ Ioo 0 a, α.eta base r' = α.eta base r + s := by
  have hev : ∀ᶠ x in nhdsWithin 0 (Set.Ioi 0), α.eta base r + s ≤ α.eta base x :=
    hdiv.eventually (Filter.eventually_ge_atTop _)
  have hIoo_nhd : Set.Ioo 0 r ∈ nhdsWithin 0 (Set.Ioi 0) := by
    rw [mem_nhdsWithin]
    exact ⟨Set.Iio r, isOpen_Iio, hr.1, fun x ⟨hlt, hgt⟩ => ⟨hgt, hlt⟩⟩
  obtain ⟨ε, hε_large, hε_ioo⟩ :=
    (hev.and (Filter.eventually_of_mem hIoo_nhd (fun x hx => hx))).exists
  have hcont_Icc : ContinuousOn (α.eta base) (Set.Icc ε r) :=
    (eta_continuousOn α base hbase).mono
      (fun x hx => ⟨lt_of_lt_of_le hε_ioo.1 hx.1, lt_of_le_of_lt hx.2 hr.2⟩)
  obtain ⟨r', hr'_icc, hr'_eq⟩ :=
    intermediate_value_Icc' (le_of_lt hε_ioo.2) hcont_Icc
      ⟨le_add_of_nonneg_right hs, hε_large⟩
  exact ⟨r', ⟨lt_of_lt_of_le hε_ioo.1 hr'_icc.1, lt_of_le_of_lt hr'_icc.2 hr.2⟩, hr'_eq⟩

/-! ### Properties of η⁻¹ -/

/-- If `t` is in the range of η on `(0, a)`, then `η⁻¹(t) ∈ (0, a)`. -/
private lemma etaInv_mem_Ioo (α : ClassK a b) (base : ℝ)
    {t : ℝ} (ht : ∃ r ∈ Ioo 0 a, α.eta base r = t) :
    α.etaInv base t ∈ Ioo 0 a := by
  simp only [ClassK.etaInv, dif_pos ht]
  exact (Classical.choose_spec ht).1

/-- Left inverse: `η(η⁻¹(t)) = t` whenever `t` is in the range of η. -/
private lemma eta_etaInv (α : ClassK a b) (base : ℝ)
    {t : ℝ} (ht : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t) :
    α.eta base (α.etaInv base t) = t := by
  simp only [ClassK.etaInv, dif_pos ht]
  exact (Classical.choose_spec ht).2

/-- Right inverse: `η⁻¹(η(r)) = r` for any `r ∈ (0, a)`. -/
private lemma etaInv_eta (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    {r : ℝ} (hr : r ∈ Set.Ioo 0 a) :
    α.etaInv base (α.eta base r) = r :=
  (eta_strictAntiOn α base hbase).injOn
    (etaInv_mem_Ioo α base ⟨r, hr, rfl⟩) hr
    (eta_etaInv α base ⟨r, hr, rfl⟩)

/-- η⁻¹ is strictly anti-monotone on the range of η:
    `t₁ < t₂` implies `η⁻¹(t₂) < η⁻¹(t₁)`, by contrapositive from anti-monotonicity of η. -/
private lemma etaInv_strictAntiOn (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    {t₁ t₂ : ℝ}
    (ht₁ : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t₁)
    (ht₂ : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t₂)
    (hlt : t₁ < t₂) :
    α.etaInv base t₂ < α.etaInv base t₁ := by
  have h₁ := etaInv_mem_Ioo α base ht₁
  have h₂ := etaInv_mem_Ioo α base ht₂
  have heq₁ := eta_etaInv α base ht₁
  have heq₂ := eta_etaInv α base ht₂
  rcases lt_or_ge (α.etaInv base t₂) (α.etaInv base t₁) with h | h
  · exact h
  · exfalso
    rcases eq_or_lt_of_le h with h_eq | hlt'
    · -- etaInv t₁ = etaInv t₂  →  t₁ = t₂
      have h_eta_eq := congr_arg (α.eta base) h_eq
      rw [heq₁, heq₂] at h_eta_eq
      linarith
    · -- etaInv t₁ < etaInv t₂  →  t₂ < t₁
      have h_eta_lt := eta_strictAntiOn α base hbase h₁ h₂ hlt'
      rw [heq₁, heq₂] at h_eta_lt
      linarith

/-- `η⁻¹(t) → 0` as `t → +∞`: large `t` forces the preimage near 0, because η is
    strictly decreasing and `η(δ)` is a finite threshold above which `η⁻¹(t) ≤ δ`. -/
private lemma etaInv_tendsto_zero (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a) :
    Filter.Tendsto (α.etaInv base) Filter.atTop (nhds 0) := by
  apply tendsto_order.mpr
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- b < 0: etaInv t ≥ 0 always, so b < etaInv t
    rw [Filter.eventually_atTop]
    refine ⟨0, fun t _ => ?_⟩
    rcases Classical.em (∃ r ∈ Set.Ioo 0 a, α.eta base r = t) with hrange | hrange
    · linarith [(etaInv_mem_Ioo α base hrange).1]
    · simp only [ClassK.etaInv, dif_neg hrange]; linarith
  · -- b > 0: use threshold M = η(δ) where δ = min(b/2, a/2)
    set δ := min (b / 2) (a / 2)
    have hδ_pos  : 0 < δ := lt_min (by linarith) (by linarith [α.ha])
    have hδ_lt_a : δ < a := lt_of_le_of_lt (min_le_right _ _) (by linarith [α.ha])
    have hδ_lt_b : δ < b := lt_of_le_of_lt (min_le_left  _ _) (by linarith)
    have hδ_ioo  : δ ∈ Set.Ioo 0 a := ⟨hδ_pos, hδ_lt_a⟩
    filter_upwards [Filter.eventually_ge_atTop (α.eta base δ)] with t ht
    rcases Classical.em (∃ r ∈ Set.Ioo 0 a, α.eta base r = t) with hrange | hrange
    · have hmem := etaInv_mem_Ioo α base hrange
      have heq  := eta_etaInv α base hrange
      have hle  : α.etaInv base t ≤ δ := by
        by_contra h; push Not at h
        -- η strictly anti-mono: δ < etaInv(t) → η(etaInv(t)) < η(δ)
        -- but η(etaInv(t)) = t ≥ η(δ). Contradiction.
        linarith [eta_strictAntiOn α base hbase hδ_ioo hmem h, heq]
      linarith
    · simp only [ClassK.etaInv, dif_neg hrange]; linarith

/-- η⁻¹ is continuous at any point in the range of η.
    Proved via the order topology: for each one-sided bound on the output, IVT on a compact
    subinterval of `(0, a)` finds a `t`-neighbourhood mapping into the desired `r`-neighbourhood. -/
private lemma etaInv_continuousAt (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    {t : ℝ} (ht : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t) :
    ContinuousAt (α.etaInv base) t := by
  /- Write `r = η⁻¹(t)`.  For any `x₁ < r < x₂` in `(0, a)`, the values `t'` strictly between
     `η(x₂)` and `η(x₁)` form a neighbourhood of `t`, and by IVT each such `t'` is `η(r')` for
     some `r' ∈ [x₁, x₂]`; so `η⁻¹(t') ∈ [x₁, x₂]`.  Given an order bound `z₁ < r` (or
     `r < z₂`), choose `x₁` between `z₁` and `r` (or `x₂` between `r` and `z₂`). -/
  have h_r_mem := etaInv_mem_Ioo α base ht
  have h_r_eq := eta_etaInv α base ht
  set r := α.etaInv base t
  have heta_inj : ∀ x ∈ Set.Ioo 0 a, ∀ y ∈ Set.Ioo 0 a,
      α.eta base x = α.eta base y → x = y :=
    (eta_strictAntiOn α base hbase).injOn
  -- Step 1. Near `η(r)`, `η⁻¹` is trapped in `[x₁, x₂]` for any `x₁ < r < x₂` in `(0, a)`.
  have h_IVT : ∀ x₁ x₂, x₁ ∈ Set.Ioo 0 a → x₂ ∈ Set.Ioo 0 a → x₁ < r → r < x₂ →
      ∀ᶠ t' in 𝓝 (α.eta base r), x₁ ≤ α.etaInv base t' ∧ α.etaInv base t' ≤ x₂ := by
    intro x₁ x₂ hx₁ hx₂ hlt₁ hlt₂
    have h_t₁ := eta_strictAntiOn α base hbase hx₁ h_r_mem hlt₁
    have h_t₂ := eta_strictAntiOn α base hbase h_r_mem hx₂ hlt₂
    filter_upwards [Ioo_mem_nhds h_t₂ h_t₁] with t' ht'
    have hcont : ContinuousOn (α.eta base) (Set.Icc x₁ x₂) :=
      (eta_continuousOn α base hbase).mono
        (fun x hx => ⟨lt_of_lt_of_le hx₁.1 hx.1, lt_of_le_of_lt hx.2 hx₂.2⟩)
    obtain ⟨r', hr'_icc, hr'_eq⟩ := intermediate_value_Icc' (le_of_lt (lt_trans hlt₁ hlt₂))
      hcont ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩
    have hr'_ioo : r' ∈ Set.Ioo 0 a :=
      ⟨lt_of_lt_of_le hx₁.1 hr'_icc.1, lt_of_le_of_lt hr'_icc.2 hx₂.2⟩
    have hetaInv_eq : α.etaInv base t' = r' :=
      heta_inj _ (etaInv_mem_Ioo α base ⟨r', hr'_ioo, hr'_eq⟩) _ hr'_ioo
        (by rw [eta_etaInv α base ⟨r', hr'_ioo, hr'_eq⟩, hr'_eq])
    rwa [hetaInv_eq]
  -- Step 2. Fixed partner points `0 < x_lo < r < x_hi < a`, one for each side.
  obtain ⟨x_lo, hx_lo_pos, hx_lo_lt⟩ := exists_between h_r_mem.1
  obtain ⟨x_hi, hx_hi_gt, hx_hi_lt⟩ := exists_between h_r_mem.2
  have hx_lo_mem : x_lo ∈ Set.Ioo 0 a := ⟨hx_lo_pos, hx_lo_lt.trans h_r_mem.2⟩
  have hx_hi_mem : x_hi ∈ Set.Ioo 0 a := ⟨h_r_mem.1.trans hx_hi_gt, hx_hi_lt⟩
  -- Step 3. Continuity in the order topology: check each one-sided bound.
  rw [ContinuousAt]
  change Filter.Tendsto (α.etaInv base) (𝓝 t) (𝓝 r)
  rw [← h_r_eq]
  apply tendsto_order.mpr
  constructor
  · -- Lower bound `z₁ < r`: pick `x₁ ∈ (max 0 z₁, r)`; then `z₁ < x₁ ≤ η⁻¹(t')`.
    intro z₁ hz₁
    obtain ⟨x₁, hx₁_gt, hx₁_lt⟩ := exists_between (max_lt h_r_mem.1 hz₁)
    have hx₁_mem : x₁ ∈ Set.Ioo 0 a :=
      ⟨(le_max_left 0 z₁).trans_lt hx₁_gt, hx₁_lt.trans h_r_mem.2⟩
    have hz₁_lt : z₁ < x₁ := (le_max_right 0 z₁).trans_lt hx₁_gt
    filter_upwards [h_IVT x₁ x_hi hx₁_mem hx_hi_mem hx₁_lt hx_hi_gt] with t' ht'
    exact hz₁_lt.trans_le ht'.1
  · -- Upper bound `r < z₂`: pick `x₂ ∈ (r, min a z₂)`; then `η⁻¹(t') ≤ x₂ < z₂`.
    intro z₂ hz₂
    obtain ⟨x₂, hx₂_gt, hx₂_lt⟩ := exists_between (lt_min h_r_mem.2 hz₂)
    have hx₂_mem : x₂ ∈ Set.Ioo 0 a :=
      ⟨h_r_mem.1.trans hx₂_gt, hx₂_lt.trans_le (min_le_left a z₂)⟩
    have hz₂_gt : x₂ < z₂ := hx₂_lt.trans_le (min_le_right a z₂)
    filter_upwards [h_IVT x_lo x₂ hx_lo_mem hx₂_mem hx_lo_lt hx₂_gt] with t' ht'
    exact ht'.2.trans_lt hz₂_gt

/-- **Osgood's condition from a linear bound.**  If `α(x) ≤ L x` on `(0, base]`, then
    `η_base(y) → +∞` as `y → 0⁺`.

    Comparing integrands, `η(y) = ∫_y^{base} 1/α ≥ ∫_y^{base} 1/(L x) = (log base − log y)/L`,
    and the right-hand side diverges as `y → 0⁺`. -/
private lemma ClassK.etaDiverges_of_le_linear {a b : ℝ} (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (L : ℝ) (hL_pos : 0 < L)
    (h_lin : ∀ x ∈ Set.Ioc 0 base, α.toFun x ≤ L * x) :
    α.EtaDiverges base := by
  -- Step 1. The logarithmic lower bound `(log base − log y)/L` diverges as `y → 0⁺`.
  have h_tendsto_log : Filter.Tendsto (fun y => (Real.log base - Real.log y) / L)
      (𝓝[>] 0) Filter.atTop := by
    have h_eq : (fun y => (Real.log base - Real.log y) / L) =
        (fun y => (1 / L) * (-Real.log y) + Real.log base / L) := by ext; ring
    rw [h_eq]
    exact (Filter.Tendsto.const_mul_atTop (one_div_pos.mpr hL_pos)
      (Filter.tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero)).atTop_add
        tendsto_const_nhds
  -- Step 2. For `0 < y < base`, it is below `∫_y^{base} 1/α`.
  have h_bound : ∀ᶠ y in 𝓝[>] 0, (Real.log base - Real.log y) / L ≤
      ∫ x in y..base, 1 / α.toFun x := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hbase.1)]
      with y hy_pos hy_lt_base
    have hx_pos : ∀ x ∈ Set.uIcc y base, 0 < x :=
      fun x hx => (lt_min hy_pos hbase.1).trans_le hx.1
    have hα_pos : ∀ x ∈ Set.Icc y base, 0 < α.toFun x := fun x hx =>
      α.pos_on_Ioo ⟨hy_pos.trans_le hx.1, hx.2.trans_lt hbase.2⟩
    -- `1/(L x)` is integrable on `[y, base]`: continuous with nonvanishing denominator.
    have h1_intble : IntervalIntegrable (fun x => 1 / (L * x)) MeasureTheory.volume y base :=
      (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
        (fun x hx => (mul_pos hL_pos (hx_pos x hx)).ne')).intervalIntegrable
    -- `1/α` is integrable on `[y, base]`: `α` is continuous and positive there.
    have h_inv_intble : IntervalIntegrable (fun x => 1 / α.toFun x) volume y base := by
      have h_sub : Set.uIcc y base ⊆ Set.Ico 0 a := fun x hx => by
        rw [Set.uIcc_of_le hy_lt_base.le] at hx
        exact ⟨hy_pos.le.trans hx.1, hx.2.trans_lt hbase.2⟩
      refine (continuousOn_const.div (α.continuous.mono h_sub) fun x hx => ?_).intervalIntegrable
      rw [Set.uIcc_of_le hy_lt_base.le] at hx
      exact (hα_pos x hx).ne'
    calc (Real.log base - Real.log y) / L
        = ∫ x in y..base, 1 / (L * x) := by
            have h_deriv : ∀ x ∈ Set.uIcc y base,
                HasDerivAt (fun t => Real.log t / L) (1 / (L * x)) x := fun x hx => by
              have h := (Real.hasDerivAt_log (hx_pos x hx).ne').div_const L
              rwa [show x⁻¹ / L = 1 / (L * x) from by rw [inv_eq_one_div]; ring] at h
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h1_intble]; ring
      _ ≤ ∫ x in y..base, 1 / α.toFun x :=
            intervalIntegral.integral_mono_on hy_lt_base.le h1_intble h_inv_intble
              fun x hx => div_le_div_of_nonneg_left zero_le_one (hα_pos x hx)
                (h_lin x ⟨hy_pos.trans_le hx.1, hx.2⟩)
  -- Step 3. `η(y) = ∫_y^{base} 1/α`, so `η` dominates a divergent function.
  exact tendsto_atTop_mono' _ (h_bound.mono fun y hy => by
    change (Real.log base - Real.log y) / L ≤ -∫ x in base..y, 1 / α.toFun x
    rwa [intervalIntegral.integral_symm, neg_neg]) h_tendsto_log


/-! ### Properties of σ -/

/-- Away from `r = 0`, `σ` is given by its defining formula `σ(r, s) = η⁻¹(η(r) + s)`. -/
private lemma sigma_of_pos (α : ClassK a b) (base : ℝ) {r : ℝ} (hr : 0 < r) {s : ℝ} :
    α.sigma base r s = α.etaInv base (α.eta base r + s) :=
  if_neg hr.ne'

/-- `σ(0, s) = 0`: the solution started at the origin stays there. -/
private lemma sigma_zero_left (α : ClassK a b) (base s : ℝ) : α.sigma base 0 s = 0 :=
  if_pos rfl

/-- `σ(r, 0) = r`: at time zero the solution is at its initial state. -/
private lemma sigma_zero_right (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    {r : ℝ} (hr : r ∈ Ioo 0 a) :
    α.sigma base r 0 = r := by
  rw [sigma_of_pos α base hr.1, add_zero]
  exact etaInv_eta α base hbase hr

/-- For `r ∈ (0, a)` and `s ≥ 0`, the state `σ(r, s)` stays in `(0, a)`: by Osgood's
    condition `η(r) + s` is a value of `η` on `(0, a)`, so `η⁻¹` maps it back there. -/
private lemma sigma_mem_Ioo (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) {r s : ℝ} (hr : r ∈ Ioo 0 a) (hs : 0 ≤ s) :
    α.sigma base r s ∈ Ioo 0 a := by
  rw [sigma_of_pos α base hr.1]
  exact etaInv_mem_Ioo α base (eta_add_mem_range α base hbase hdiv hr hs)

/-- Comparison of two interior values of `σ`: a smaller time-to-go argument `η(r) + s` means a
    larger state, because `η⁻¹` is strictly decreasing. -/
private lemma sigma_lt_sigma (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) {r₁ r₂ s₁ s₂ : ℝ} (hr₁ : r₁ ∈ Ioo 0 a) (hr₂ : r₂ ∈ Ioo 0 a)
    (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (h : α.eta base r₂ + s₂ < α.eta base r₁ + s₁) :
    α.sigma base r₁ s₁ < α.sigma base r₂ s₂ := by
  rw [sigma_of_pos α base hr₁.1, sigma_of_pos α base hr₂.1]
  exact etaInv_strictAntiOn α base hbase (eta_add_mem_range α base hbase hdiv hr₂ hs₂)
    (eta_add_mem_range α base hbase hdiv hr₁ hs₁) h

/-- `σ ≥ 0` on `[0, a) × [0, ∞)`: either `r = 0` and `σ = 0`, or `σ(r, s) ∈ (0, a)`. -/
private lemma sigma_nonneg (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) {r s : ℝ} (hr : r ∈ Ico 0 a) (hs : 0 ≤ s) :
    0 ≤ α.sigma base r s := by
  rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
  · -- Case `r = 0`: `σ(0, s) = 0`.
    exact (sigma_zero_left α base s).ge
  · -- Case `r > 0`: `σ(r, s) ∈ (0, a)`.
    exact (sigma_mem_Ioo α base hbase hdiv ⟨hr_pos, hr.2⟩ hs).1.le

/-- `σ(r, s) ≤ r` on `[0, a) × [0, ∞)`: the solution never rises above its initial state. -/
private lemma sigma_le_self (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) {r s : ℝ} (hr : r ∈ Ico 0 a) (hs : 0 ≤ s) :
    α.sigma base r s ≤ r := by
  rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
  · -- Case `r = 0`: `σ(0, s) = 0`.
    exact (sigma_zero_left α base s).le
  · have hr' : r ∈ Ioo 0 a := ⟨hr_pos, hr.2⟩
    rcases eq_or_lt_of_le hs with rfl | hs_pos
    · -- Case `s = 0`: `σ(r, 0) = r`.
      exact (sigma_zero_right α base hbase hr').le
    · -- Case `s > 0`: `η(r) + 0 < η(r) + s`, so `σ(r, s) < σ(r, 0) = r`.
      have h_lt : α.sigma base r s < α.sigma base r 0 :=
        sigma_lt_sigma α base hbase hdiv hr' hr' hs le_rfl (by linarith)
      exact (h_lt.trans_eq (sigma_zero_right α base hbase hr')).le

/-- Near an interior initial state `r ∈ (0, a)`, `σ` is jointly continuous: there it equals
    `η⁻¹(η(p.1) + p.2)`, a composition of continuous maps. -/
private lemma sigma_continuousAt_of_pos (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) {r s : ℝ} (hr : r ∈ Ioo 0 a) (hs : 0 ≤ s) :
    ContinuousAt (Function.uncurry (α.sigma base)) (r, s) := by
  -- Near `(r, s)` the first coordinate is positive, so `σ` is given by its formula.
  have h_eq : (fun p : ℝ × ℝ => α.etaInv base (α.eta base p.1 + p.2)) =ᶠ[𝓝 (r, s)]
      Function.uncurry (α.sigma base) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hr.1)]
      with p hp
    exact (sigma_of_pos α base hp).symm
  -- Inner map `p ↦ η(p.1) + p.2`: `η` is differentiable, hence continuous, at `r`.
  have h_eta : ContinuousAt (α.eta base) r := (eta_hasDerivAt α base hbase hr).continuousAt
  have h_eta_fst : ContinuousAt (fun p : ℝ × ℝ => α.eta base p.1) (r, s) :=
    ContinuousAt.comp (g := α.eta base) (f := Prod.fst) h_eta continuousAt_fst
  have h_inner : ContinuousAt (fun p : ℝ × ℝ => α.eta base p.1 + p.2) (r, s) :=
    h_eta_fst.add continuousAt_snd
  -- Outer map `η⁻¹`: continuous at `η(r) + s`, which is in the range of `η`.
  have h_outer : ContinuousAt (α.etaInv base) (α.eta base r + s) :=
    etaInv_continuousAt α base hbase (eta_add_mem_range α base hbase hdiv hr hs)
  have h_comp : ContinuousAt (fun p : ℝ × ℝ => α.etaInv base (α.eta base p.1 + p.2)) (r, s) :=
    ContinuousAt.comp (g := α.etaInv base) h_outer h_inner
  exact h_comp.congr h_eq

/-- **KL field `continuous`.**  `σ` is jointly continuous on `[0, a) × [0, ∞)`. -/
private lemma sigma_continuousOn (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) :
    ContinuousOn (Function.uncurry (α.sigma base)) (Ico 0 a ×ˢ Ici 0) := by
  rintro ⟨r, s⟩ ⟨hr, hs⟩
  rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
  · -- Case `r = 0`: squeeze `0 ≤ σ(p) ≤ p.1`, and `p.1 → 0`.
    have h_lower : ∀ᶠ p in 𝓝[Ico 0 a ×ˢ Ici 0] ((0 : ℝ), s),
        0 ≤ Function.uncurry (α.sigma base) p :=
      eventually_nhdsWithin_of_forall fun p hp => sigma_nonneg α base hbase hdiv hp.1 hp.2
    have h_upper : ∀ᶠ p in 𝓝[Ico 0 a ×ˢ Ici 0] ((0 : ℝ), s),
        Function.uncurry (α.sigma base) p ≤ p.1 :=
      eventually_nhdsWithin_of_forall fun p hp => sigma_le_self α base hbase hdiv hp.1 hp.2
    rw [ContinuousWithinAt, Function.uncurry_apply_pair, sigma_zero_left]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      continuous_fst.continuousWithinAt h_lower h_upper
  · -- Case `r > 0`: `σ` is continuous at `(r, s)` outright.
    exact (sigma_continuousAt_of_pos α base hbase hdiv ⟨hr_pos, hr.2⟩ hs).continuousWithinAt

/-- **KL field `strict_mono_r`.**  For fixed `s ≥ 0`, `σ(·, s)` is strictly increasing. -/
private lemma sigma_strictMonoOn_r (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) :
    ∀ s ≥ 0, StrictMonoOn (fun r => α.sigma base r s) (Ico 0 a) := by
  intro s hs r₁ hr₁ r₂ hr₂ hr_lt
  dsimp only
  have hr₂' : r₂ ∈ Ioo 0 a := ⟨hr₁.1.trans_lt hr_lt, hr₂.2⟩
  rcases eq_or_lt_of_le hr₁.1 with rfl | hr₁_pos
  · -- Case `r₁ = 0`: `σ(0, s) = 0 < σ(r₂, s)`.
    rw [sigma_zero_left]
    exact (sigma_mem_Ioo α base hbase hdiv hr₂' hs).1
  · -- Case `0 < r₁ < r₂`: `η(r₂) < η(r₁)`, and `η⁻¹` reverses the order again.
    have hr₁' : r₁ ∈ Ioo 0 a := ⟨hr₁_pos, hr₁.2⟩
    have h_eta_lt := eta_strictAntiOn α base hbase hr₁' hr₂' hr_lt
    exact sigma_lt_sigma α base hbase hdiv hr₁' hr₂' hs hs (by linarith)

/-- **KL field `anti_s`.**  For fixed `r`, `σ(r, ·)` is nonincreasing: a later time means a
    larger argument `η(r) + s` to the decreasing map `η⁻¹`. -/
private lemma sigma_antitoneOn_s (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base) :
    ∀ r ∈ Ico 0 a, AntitoneOn (fun s => α.sigma base r s) (Ici 0) := by
  intro r hr s₁ hs₁ s₂ hs₂ hs_le
  dsimp only
  rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
  · -- Case `r = 0`: both sides vanish.
    simp only [sigma_zero_left, le_refl]
  · have hr' : r ∈ Ioo 0 a := ⟨hr_pos, hr.2⟩
    rcases eq_or_lt_of_le hs_le with rfl | hs_lt
    · -- Case `s₁ = s₂`.
      exact le_rfl
    · -- Case `s₁ < s₂`.
      exact (sigma_lt_sigma α base hbase hdiv hr' hr' hs₂ hs₁ (by linarith)).le

/-- **KL field `tendsto_zero`.**  `σ(r, s) → 0` as `s → ∞`: the argument `η(r) + s` tends to
    `+∞`, and `η⁻¹(t) → 0` as `t → ∞`. -/
private lemma sigma_tendsto_zero (α : ClassK a b) (base : ℝ) (hbase : base ∈ Ioo 0 a) :
    ∀ r ∈ Ico 0 a, Tendsto (fun s => α.sigma base r s) atTop (𝓝 0) := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
  · -- Case `r = 0`: `σ(0, ·)` is identically `0`.
    simp only [sigma_zero_left]
    exact tendsto_const_nhds
  · -- Case `r > 0`: compose `η⁻¹ → 0` with `s ↦ η(r) + s → ∞`.
    simp only [sigma_of_pos α base hr_pos]
    exact (etaInv_tendsto_zero α base hbase).comp
      (tendsto_atTop_add_const_left _ (α.eta base r) tendsto_id)

/-! ### The σ function is Class KL -/

/-- **Osgood construction:** given `α : ClassK a b` satisfying the Osgood condition
    (`EtaDiverges`), `σ(r, s) = η⁻¹(η(r) + s)` extended by `σ(0, s) = 0` is Class KL. -/
private theorem ClassK.sigma_isClassKL (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (L : ℝ) (hL_pos : 0 < L)
    (hLip : ∀ x ∈ Set.Ioc 0 base, α.toFun x ≤ L * x) :
    ∃ σ : ClassKL a,
      (∀ r ∈ Set.Ioo 0 a, ∀ s ≥ 0, σ.toFun r s = α.sigma base r s) ∧
      (∀ s ≥ 0, σ.toFun 0 s = 0) := by
  /- The linear bound gives Osgood's condition; with it, each class KL field is one of the
     `sigma_*` lemmas above. -/
  have hdiv : α.EtaDiverges base :=
    ClassK.etaDiverges_of_le_linear α base hbase L hL_pos hLip
  refine ⟨{
    ha            := α.ha
    toFun         := α.sigma base
    map_zero      := fun s _ => sigma_zero_left α base s
    continuous    := sigma_continuousOn α base hbase hdiv
    strict_mono_r := sigma_strictMonoOn_r α base hbase hdiv
    nonneg        := fun _ hr _ hs => sigma_nonneg α base hbase hdiv hr hs
    anti_s        := sigma_antitoneOn_s α base hbase hdiv
    tendsto_zero  := sigma_tendsto_zero α base hbase
  }, fun _ _ _ _ => rfl, fun s _ => sigma_zero_left α base s⟩


private lemma ClassK.sigma_hasDerivAt {a b : ℝ} (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (L : ℝ) (hL_pos : 0 < L)
    (hLip : ∀ x ∈ Set.Ioc 0 base, α.toFun x ≤ L * x)
    (r : ℝ) (hr : r ∈ Set.Ioo 0 a) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun x => α.sigma base r x) (- α.toFun (α.sigma base r s)) s := by
  simp only [ClassK.sigma, if_neg hr.1.ne']
  -- Establish η(r) + s is in the range of η
  have hdiv := etaDiverges_of_le_linear α base hbase L hL_pos hLip
  have ht₀_range : ∃ r' ∈ Set.Ioo 0 a, α.eta base r' = α.eta base r + s :=
    eta_add_mem_range α base hbase hdiv hr hs.le
  have hy₀_mem : α.etaInv base (α.eta base r + s) ∈ Set.Ioo 0 a :=
    etaInv_mem_Ioo α base ht₀_range
  have h_cont : ContinuousAt (α.etaInv base) (α.eta base r + s) :=
    etaInv_continuousAt α base hbase ht₀_range
  -- Derivative of etaInv via HasDerivAt.of_local_left_inverse
  have h_etaInv_deriv : HasDerivAt (α.etaInv base)
      (-α.toFun (α.etaInv base (α.eta base r + s))) (α.eta base r + s) := by
    have h_eta_der := eta_hasDerivAt α base hbase hy₀_mem
    have h_ne : -1 / α.toFun (α.etaInv base (α.eta base r + s)) ≠ 0 :=
      div_ne_zero (by norm_num) ((α.pos_on_Ioo hy₀_mem).ne')
    have h_local_inv : ∀ᶠ y in 𝓝 (α.eta base r + s), α.eta base (α.etaInv base y) = y := by
      filter_upwards [h_cont.preimage_mem_nhds (Ioo_mem_nhds hy₀_mem.1 hy₀_mem.2)] with y hy
      have h_in_range : ∃ r' ∈ Set.Ioo 0 a, α.eta base r' = y := by
        by_contra h
        simp  [ClassK.etaInv, dif_neg h, Set.mem_Ioo, false_and] at hy
      exact eta_etaInv α base h_in_range
    convert h_eta_der.of_local_left_inverse h_cont h_ne h_local_inv using 1
    simp only [neg_div, neg_inv, one_div, inv_inv]
  -- Chain rule: (fun x => etaInv(η(r) + x))' = (-α(y₀)) * 1
  have h_linear : HasDerivAt (fun x => α.eta base r + x) 1 s :=
    (hasDerivAt_id s).const_add _
  have h_chain := h_etaInv_deriv.comp s h_linear
  simp only [mul_one] at h_chain
  exact h_chain


end OsgoodConstruction


/-! ## The decay ODE has a class KL solution operator -/

/-- **The decay ODE `ẏ = −α(y)` admits a class KL solution operator.**

If `α` is at most linear near the origin — so that the origin is not reached in finite time —
then there is a class KL function `σ` such that `s ↦ σ(r, s)` is the solution of `ẏ = −α(y)`
started at `r`.

This is the only thing the rest of the library needs from the Osgood construction. Stating it
this way keeps the construction itself — the time-to-reach integral, its inverse, and the
closed form built from them — inside the proof, where it belongs: those are steps in building
a solution, not results about class K functions. 

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.4. Differences:
- Khalil assumes `α` locally Lipschitz; here the hypothesis is the linear bound `α(x) ≤ L·x`
  near the origin, which is what the construction uses.
- Uniqueness of the solution is not asserted, only existence of the class `KL` operator `σ`. -/
@[blueprint "thm:class-KL-osgood"
  (title := "The decay ODE has a class $\\mathcal{KL}$ solution operator")
  (statement := /-- Let $\alpha$ be class $\mathcal{K}$ on $[0,a)$ and at most linear near the
    origin,
    $\alpha(x) \le Lx$ on $(0, \mathrm{base}]$.  Then there is a class $\mathcal{KL}$
    function $\sigma$ (\cref{def:isClassKL}) with $\sigma(0, s) = 0$, $\sigma(r, 0) = r$,
    and such that for each $r$ the map $s \mapsto \sigma(r, s)$ solves
    \[
      \dot y = -\alpha(y), \qquad y(0) = r .
    \]
    That is: the decay ODE's solution operator is itself a class $\mathcal{KL}$ function.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.4.  Differences: \begin{itemize}
    \item Khalil assumes $\alpha$ locally Lipschitz; here the hypothesis is the linear bound
    $\alpha(x) \le Lx$ near the origin, which is what the construction uses. \item Uniqueness of the
    solution is not asserted, only existence of the class $\mathcal{KL}$ operator $\sigma$.
    \end{itemize}
  -/)
  (proof := /-- \textbf{Osgood's construction.}  Let
    $\eta(y) = -\int_{\mathrm{base}}^{y} \mathrm{d}x/\alpha(x)$ be the time for the solution
    started at $\mathrm{base}$ to reach $y$.  Since $\alpha > 0$ on $(0,a)$, $\eta$ is
    continuous and strictly decreasing there; and since $\alpha(x) \le Lx$ near $0$,
    \[
      \eta(y) \;\ge\; \int_{y}^{\mathrm{base}} \frac{\mathrm{d}x}{Lx}
        \;=\; \frac{\log(\mathrm{base}) - \log y}{L} \;\longrightarrow\; +\infty
      \qquad (y \to 0^{+}),
    \]
    so the origin is not reached in finite time and every value above $\eta(r)$ is attained.
    Setting $\sigma(r,s) := \eta^{-1}(\eta(r) + s)$, extended by $\sigma(0,s) = 0$, advancing
    time by $s$ moves $\eta$ up by $s$ and hence moves the state down; the class
    $\mathcal{KL}$ conditions follow from monotonicity and continuity of $\eta^{-1}$, and
    differentiating $\eta(\sigma) = \eta(r) + s$ gives $\dot\sigma = -\alpha(\sigma)$.

    The construction is local to this proof: $\eta$ and $\eta^{-1}$ are steps in building a
    solution, not results about class $\mathcal{K}$ functions. -/)]
theorem ClassK.exists_classKL_decaySolution (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (L : ℝ) (hL_pos : 0 < L)
    (hLip : ∀ x ∈ Set.Ioc 0 base, α.toFun x ≤ L * x) :
    ∃ σ : ClassKL a,
      (∀ s ≥ 0, σ.toFun 0 s = 0) ∧
      (∀ r ∈ Set.Ico 0 a, σ.toFun r 0 = r) ∧
      (∀ r ∈ Set.Ico 0 a, ∀ s > 0,
        HasDerivAt (fun x => σ.toFun r x) (-α.toFun (σ.toFun r s)) s) := by
  obtain ⟨σ, hσ_eq, hσ_zero_s⟩ := ClassK.sigma_isClassKL α base hbase L hL_pos hLip
  refine ⟨σ, hσ_zero_s, fun r hr => ?_, fun r hr s hs => ?_⟩
  · -- σ(r, 0) = r: the solution starts where it is told to (at `r = 0`, both sides vanish)
    rcases eq_or_lt_of_le hr.1 with h_eq | hr_pos
    · rw [← h_eq]; exact hσ_zero_s 0 le_rfl
    · rw [hσ_eq r ⟨hr_pos, hr.2⟩ 0 le_rfl]
      exact sigma_zero_right α base hbase ⟨hr_pos, hr.2⟩
  · -- σ(r, ·) solves the ODE.  At `r = 0` the solution is the constant `0`, which solves it
    -- because `α 0 = 0`; away from `0` it is the Osgood construction.
    rcases eq_or_lt_of_le hr.1 with h_eq | hr_pos
    · have hconst : (fun x => σ.toFun r x) =ᶠ[nhds s] (fun _ : ℝ => (0 : ℝ)) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs)
          fun x hx => by rw [← h_eq]; exact hσ_zero_s x hx.le
      have hzero : σ.toFun r s = 0 := by rw [← h_eq]; exact hσ_zero_s s hs.le
      rw [hzero, α.map_zero, neg_zero]
      exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hconst
    · have hr' : r ∈ Set.Ioo 0 a := ⟨hr_pos, hr.2⟩
      have hderiv := ClassK.sigma_hasDerivAt α base hbase L hL_pos hLip r hr' s hs
      have hfun : (fun x => σ.toFun r x) =ᶠ[nhds s] (fun x => α.sigma base r x) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs)
          fun x hx => hσ_eq r hr' x (le_of_lt hx)
      have hval : -α.toFun (α.sigma base r s) = -α.toFun (σ.toFun r s) := by
        rw [hσ_eq r hr' s hs.le]
      exact (hval ▸ hderiv).congr_of_eventuallyEq hfun

/-! ## Comparison bound from Dini ≤ −ClassK -/

/-- **Comparison KL bound**: for any class K function `α`, there exists a class KL function `σ`
    such that any continuous scalar function `v` with upper-right Dini derivative
    `D⁺v(s) ≤ −α(v(s))`, starting and remaining in `[0, a)`, satisfies
    `v(t) ≤ σ(v(t₀), t − t₀)`.

    The class K decay ODE `ẏ = −α(y)` determines σ; the comparison lemma supplies the
    bound. All ODE infrastructure (Lipschitz minorant, Osgood construction,
    Picard–Lindelöf) is hidden inside. -/
@[blueprint "thm:classK-dini-bound"
  (title := "Comparison bound from a Dini decay condition")
  (statement := /-- Let $\alpha$ be
    class $\mathcal{K}$ on $[0,a)$.  Then there is a class $\mathcal{KL}$ function $\sigma$
    with $\sigma(r,0) \le r$ such that: whenever $v$ is continuous on $[t_0,t]$, takes values
    in $[0,a)$ there, has bounded forward difference quotients, and satisfies the Dini
    inequality
    \[
      D^{+}v(s) \;\le\; -\alpha(v(s)),
    \]
    it obeys $v(t) \le \sigma\bigl(v(t_0),\, t - t_0\bigr)$.

    A differential \emph{inequality} with a class $\mathcal{K}$ decay rate therefore yields a
    class $\mathcal{KL}$ bound — which is what converts a Lyapunov decay estimate into an
    asymptotic stability statement.  No hypothesis is placed on $\alpha$ beyond being class
    $\mathcal{K}$: the linear-growth condition the construction needs is obtained internally by
    passing to a Lipschitz minorant. -/)
  (proof := /-- Replace $\alpha$ by a class $\mathcal{K}$ minorant $\beta \le \alpha$ that is
    Lipschitz near the origin; this only weakens the Dini hypothesis, and supplies the linear
    bound $\beta(x) \le Lx$ that \cref{thm:class-KL-osgood} requires.  That theorem gives a
    class $\mathcal{KL}$ $\sigma$ whose sections solve $\dot y = -\beta(y)$ with
    $\sigma(r,0) = r$.  Since $v$ is a Dini subsolution of the same equation and starts at
    $\sigma(v(t_0), 0)$, \cref{thm:comparison-lemma} bounds $v$ by it — the perturbed
    solutions that lemma requires coming from
    \cref{thm:exists-isIntegralSolution-Icc-of-lipschitz}, whose hypotheses hold because
    $\beta$ is globally Lipschitz (\cref{lem:exists-classK-minorant-lipschitz}). -/)]
lemma classK_dini_bound {a b : ℝ} (α : ClassK a b) :
    ∃ σ : ClassKL a,
      (∀ r ∈ Set.Ico 0 a, σ.toFun r 0 ≤ r) ∧
      ∀ {t₀ t : ℝ}, t₀ ≤ t → ∀ (v : ℝ → ℝ), ContinuousOn v (Set.Icc t₀ t) →
        v t₀ ∈ Set.Ico 0 a →
        (∀ s ∈ Set.Ico t₀ t, v s ∈ Set.Ico 0 a) →
        (∀ s ∈ Set.Ico t₀ t, D⁺ v s ≤ -α.toFun (v s)) →
        (∀ s ∈ Set.Ico t₀ t,
            IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (s + h) - v s) / h)) →
        v t ≤ σ.toFun (v t₀) (t - t₀) := by
  obtain ⟨_, L, β, hL_pos, hβ_le_α, hβ_lin, hLip⟩ := exists_classK_minorant_lipschitz α
  have h_base : a / 2 ∈ Set.Ioo 0 a := ⟨half_pos α.ha, half_lt_self α.ha⟩
  obtain ⟨σ, hσ_zero_s, hσ_init, hσ_deriv⟩ :=
    ClassK.exists_classKL_decaySolution β (a / 2) h_base L hL_pos
      fun x hx => hβ_lin x hx.1.le
  refine ⟨σ, ?_, ?_⟩
  · -- σ(r, 0) ≤ r for r ∈ [0, a)
    intro r hr
    exact le_of_eq (hσ_init r hr)
  · -- Trajectory bound
    intro t₀ t ht v hv_cont hv₀ hv_range hDv hv_bdd
    rcases eq_or_lt_of_le ht with rfl | ht_lt
    · simp only [sub_self]
      exact le_of_eq (hσ_init (v t₀) hv₀).symm
    · -- Strengthen: D⁺v ≤ -α(v) ≤ -β(v)
      have hDv' : ∀ s ∈ Set.Ico t₀ t, D⁺ v s ≤ (fun _ x => -β.toFun x) s (v s) := by
        intro s hs
        have h1 : D⁺ v s ≤ -α.toFun (v s) := hDv s hs
        have h2 : β.toFun (v s) ≤ α.toFun (v s) := hβ_le_α (v s) (hv_range s hs)
        linarith
      -- σ satisfies the comparison ODE u̇ = -β(u)
      have hu_deriv : ∀ s ∈ Set.Ioo t₀ t,
          HasDerivAt (fun x => σ.toFun (v t₀) (x - t₀))
            ((fun _ x => -β.toFun x) s (σ.toFun (v t₀) (s - t₀))) s := by
        intro s hs
        have hs_sub_pos : 0 < s - t₀ := sub_pos.mpr hs.1
        -- σ(v t₀, ·) solves the decay ODE; compose with the shift `· - t₀`
        have h_comp := (hσ_deriv (v t₀) hv₀ (s - t₀) hs_sub_pos).comp s
          ((hasDerivAt_id s).sub_const t₀)
        simpa only [mul_one] using h_comp
      -- σ is continuous on [t₀, t]
      have hu_cont : ContinuousOn (fun s => σ.toFun (v t₀) (s - t₀)) (Set.Icc t₀ t) :=
        (σ.continuous.comp
          (continuousOn_const.prodMk (continuousOn_id.sub continuousOn_const))
          (fun s hs => ⟨hv₀, Set.mem_Ici.mpr (sub_nonneg.mpr hs.1)⟩)).congr
          (fun s _ => rfl)
      -- σ(v t₀, 0) = v t₀ (initial condition)
      have hu₀ : (fun s => σ.toFun (v t₀) (s - t₀)) t₀ = v t₀ := by
        simp only [sub_self]; exact hσ_init (v t₀) hv₀
      -- Apply comparison_lemma
      have h_bound : ∀ s ∈ Set.Icc t₀ t, v s ≤ σ.toFun (v t₀) (s - t₀) :=
        comparison_lemma (f := fun _ x => -β.toFun x) ht_lt hL_pos
          ((hLip.continuous.neg.comp continuous_snd))
          (fun _ _ => hLip.neg)
          hu_deriv hu_cont hu₀
          hv_cont hDv' hv_bdd le_rfl
          (fun lam _ =>
            exists_isIntegralSolution_Icc_of_lipschitz (g := fun _ x => -β.toFun x + lam)
              ((hLip.continuous.neg.add continuous_const).comp continuous_snd)
              (fun _ => lipschitzWith_add_const hLip.neg lam) ht_lt.le)
      exact h_bound t ⟨ht_lt.le, le_rfl⟩
