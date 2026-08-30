import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Comparison.ClassKL
import LeanForControl.Comparison.Axioms
import LeanForControl.Dini.DiniDeriv
import LeanForControl.ODEs.ComparisonLemma
import LeanForControl.ODEs.ODE_properties
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.MetricSpace.Basic
import Architect


/-!
# `Stability.ClassKDecay`

Class KL bound from the scalar decay ODE `ẏ = -α(y)` with `α ∈ ClassK`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Appendix C.

## Main result

**Osgood's construction** (`ClassK.sigma_isClassKL`): Given a class K function `α : ClassK a b`
satisfying the Osgood condition (`ClassK.EtaDiverges`), the solution `σ(r, s)` of
`ẏ = -α(y)` with `y(0) = r` is class KL in `(r, s)`.

## Construction

The solution `σ(r, s) = η⁻¹(η(r) + s)` is built from the time-to-go integral
`η(y) = -∫_{base}^y 1/α(x) dx` (`ClassK.eta`), which is strictly decreasing on `(0, a)`
and satisfies `η(y) → +∞` as `y → 0⁺` (the Osgood / finite-escape-time condition
`ClassK.EtaDiverges`). The class KL candidate is then:

  `σ(r, s) = η⁻¹(η(r) + s)`,    `σ(0, s) = 0`.

Increasing `s` shifts the argument of `η⁻¹` toward `+∞`, driving the output toward `0`.
Increasing `r` decreases `η(r)`, and since `η⁻¹` is anti-monotone, the output grows.

## Key lemmas

* `eta_hasDerivAt` — FTC derivative of η.
* `eta_strictAntiOn` — η is strictly decreasing.
* `etaInv_tendsto_zero` — η⁻¹(t) → 0 as t → +∞ (key for the KL decay condition).
* `etaInv_continuousAt` — continuity of η⁻¹ via the order-topology IVT criterion.
-/

open Set Filter Topology MeasureTheory intervalIntegral

private lemma ClassK.pos_on_Ioo (α : ClassK a b) {x : ℝ} (hx : x ∈ Ioo 0 a) :
    0 < α.toFun x :=
  (α.pos_iff ⟨hx.1.le, hx.2⟩).mpr hx.1


section OsgoodConstruction

variable {a b : ℝ}

/-! ### Definitions -/

/-- The *time-to-go* integral: `η_base(y) = −∫_{base}^y 1/α(x) dx`.
    Strictly decreasing on `(0, a)` because `α > 0` makes the integrand positive. -/
noncomputable def ClassK.eta (α : ClassK a b) (base y : ℝ) : ℝ :=
  -∫ x in base..y, (1 / α.toFun x)

/-- The Osgood condition: `η_base(y) → +∞` as `y → 0⁺`.
    This ensures the system `ẏ = −α(y)` never reaches the origin in finite time. -/
def ClassK.EtaDiverges (α : ClassK a b) (base : ℝ) : Prop :=
  Filter.Tendsto (α.eta base) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop

open Classical in
/-- The partial inverse of η: `etaInv base t` is the unique `r ∈ (0, a)` with `η(r) = t`,
    or `0` if no such `r` exists (outside the range of η). -/
noncomputable def ClassK.etaInv (α : ClassK a b) (base : ℝ) : ℝ → ℝ :=
  fun t => if h : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t
           then Classical.choose h
           else 0

/-- The Class KL candidate: `σ(r, s) = η⁻¹(η(r) + s)`, extended by `σ(0, s) = 0`
    to avoid the singularity of η at the origin. -/
noncomputable def ClassK.sigma (α : ClassK a b) (base r s : ℝ) : ℝ :=
  if r = 0 then 0 else α.etaInv base (α.eta base r + s)

/-! ### Properties of η -/

/-- **FTC:** the derivative of `η_base` at `y ∈ (0, a)` is `−1/α(y)`.
    Requires `1/α` to be interval-integrable and strongly measurable near `y`,
    both of which follow from continuity of `1/α` on `(0, a)`. -/
lemma eta_hasDerivAt (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a)
    {y : ℝ} (hy : y ∈ Ioo 0 a) :
    HasDerivAt (α.eta base) (-1 / α.toFun y) y := by
    have hcont_inv: ContinuousOn (fun x => 1 / α.toFun x) (Ioo 0 a) :=
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
    have := hderiv.neg
    simp only at this
    convert this using 1
    ring

/-- η is strictly anti-monotone on `(0, a)`: `α > 0` implies `η' = −1/α < 0` throughout. -/
lemma eta_strictAntiOn (α : ClassK a b) (base : ℝ)
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
lemma eta_continuousOn (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a) :
    ContinuousOn (α.eta base) (Ioo 0 a) := fun _ hy =>
    (eta_hasDerivAt α base hbase hy).continuousAt.continuousWithinAt

/-- For `r ∈ (0, a)` and `s ≥ 0`, the value `η(r) + s` lies in the range of η on `(0, a)`.
    `EtaDiverges` supplies `ε` near 0 with `η(ε) ≥ η(r) + s`; IVT on `[ε, r]` gives the witness. -/
lemma eta_add_mem_range (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Ioo 0 a)
    (hdiv : α.EtaDiverges base)
    {r : ℝ} (hr : r ∈ Ioo 0 a) {s : ℝ} (hs : 0 ≤ s) :
    ∃ r' ∈ Ioo 0 a, α.eta base r' = α.eta base r + s:= by
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
lemma etaInv_mem_Ioo (α : ClassK a b) (base : ℝ)
    {t : ℝ} (ht : ∃ r ∈ Ioo 0 a, α.eta base r = t) :
    α.etaInv base t ∈ Ioo 0 a := by
  simp only [ClassK.etaInv, dif_pos ht]
  exact (Classical.choose_spec ht).1

/-- Left inverse: `η(η⁻¹(t)) = t` whenever `t` is in the range of η. -/
lemma eta_etaInv (α : ClassK a b) (base : ℝ)
    {t : ℝ} (ht : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t) :
    α.eta base (α.etaInv base t) = t := by
  simp only [ClassK.etaInv, dif_pos ht]
  exact (Classical.choose_spec ht).2

/-- Right inverse: `η⁻¹(η(r)) = r` for any `r ∈ (0, a)`. -/
lemma etaInv_eta (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    {r : ℝ} (hr : r ∈ Set.Ioo 0 a) :
    α.etaInv base (α.eta base r) = r :=
  (eta_strictAntiOn α base hbase).injOn
    (etaInv_mem_Ioo α base ⟨r, hr, rfl⟩) hr
    (eta_etaInv α base ⟨r, hr, rfl⟩)

/-- η⁻¹ is strictly anti-monotone on the range of η:
    `t₁ < t₂` implies `η⁻¹(t₂) < η⁻¹(t₁)`, by contrapositive from anti-monotonicity of η. -/
lemma etaInv_strictAntiOn (α : ClassK a b) (base : ℝ)
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
      have := congr_arg (α.eta base) h_eq
      rw [heq₁, heq₂] at this
      linarith
    · -- etaInv t₁ < etaInv t₂  →  t₂ < t₁
      have := eta_strictAntiOn α base hbase h₁ h₂ hlt'
      rw [heq₁, heq₂] at this
      linarith

/-- `η⁻¹(t) → 0` as `t → +∞`: large `t` forces the preimage near 0, because η is
    strictly decreasing and `η(δ)` is a finite threshold above which `η⁻¹(t) ≤ δ`. -/
lemma etaInv_tendsto_zero (α : ClassK a b) (base : ℝ)
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
lemma etaInv_continuousAt (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    {t : ℝ} (ht : ∃ r ∈ Set.Ioo 0 a, α.eta base r = t) :
    ContinuousAt (α.etaInv base) t := by
  have h_r_mem := etaInv_mem_Ioo α base ht
  have h_r_eq := eta_etaInv α base ht
  set r := α.etaInv base t
  have heta_inj : ∀ x ∈ Set.Ioo 0 a, ∀ y ∈ Set.Ioo 0 a, α.eta base x = α.eta base y → x = y := by
    exact (eta_strictAntiOn α base hbase).injOn
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
  rw [ContinuousAt]
  change Filter.Tendsto (α.etaInv base) (𝓝 t) (𝓝 r)
  rw [← h_r_eq]
  apply tendsto_order.mpr
  constructor
  · -- Lower bound: z₁ < r
    intro z₁ hz₁
    set x₁ := (max 0 z₁ + r) / 2
    set x₂ := (r + a) / 2
    have h_max_lt : max 0 z₁ < r := max_lt h_r_mem.1 hz₁
    have h_max_ge : 0 ≤ max 0 z₁ := le_max_left 0 z₁
    -- Prove bounds on the explicit formulas so linarith can see the math
    have hx₁_pos : 0 < (max 0 z₁ + r) / 2 := by linarith
    have hx₁_lt_r : (max 0 z₁ + r) / 2 < r := by linarith
    have hx₂_gt_r : r < (r + a) / 2 := by linarith [h_r_mem.2]
    have hx₂_lt_a : (r + a) / 2 < a := by linarith [h_r_mem.2]
    have hx₁_mem : x₁ ∈ Set.Ioo 0 a := ⟨hx₁_pos, lt_trans hx₁_lt_r h_r_mem.2⟩
    have hx₂_mem : x₂ ∈ Set.Ioo 0 a := ⟨lt_trans h_r_mem.1 hx₂_gt_r, hx₂_lt_a⟩
    filter_upwards [h_IVT x₁ x₂ hx₁_mem hx₂_mem hx₁_lt_r hx₂_gt_r] with t' ht'
    linarith [ht'.1, show z₁ < x₁ by grind]
  · -- Upper bound: z₂ > r
    intro z₂ hz₂
    set x₁ := r / 2
    set x₂ := (r + min a z₂) / 2
    have h_min_gt : r < min a z₂ := lt_min h_r_mem.2 hz₂
    have h_min_le_a : min a z₂ ≤ a := min_le_left a z₂
    -- Prove bounds on the explicit formulas
    have hx₁_pos : 0 < r / 2 := by linarith [h_r_mem.1]
    have hx₁_lt_r : r / 2 < r := by linarith [h_r_mem.1]
    have hx₂_gt_r : r < (r + min a z₂) / 2 := by linarith
    have hx₂_lt_a : (r + min a z₂) / 2 < a := by linarith
    have hx₁_mem : x₁ ∈ Set.Ioo 0 a := ⟨hx₁_pos, lt_trans hx₁_lt_r h_r_mem.2⟩
    have hx₂_mem : x₂ ∈ Set.Ioo 0 a := ⟨lt_trans h_r_mem.1 hx₂_gt_r, hx₂_lt_a⟩
    filter_upwards [h_IVT x₁ x₂ hx₁_mem hx₂_mem hx₁_lt_r hx₂_gt_r] with t' ht'
    linarith [ht'.2, show x₂ < z₂ by grind [min_le_right a z₂]]


lemma ClassK.etaDiverges_of_le_linear {a b : ℝ} (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (L : ℝ) (hL_pos : 0 < L)
    (h_lin : ∀ x ∈ Set.Ioc 0 base, α.toFun x ≤ L * x) :
    α.EtaDiverges base := by
  have h_tendsto_log : Filter.Tendsto (fun y => (Real.log base - Real.log y) / L)
      (𝓝[>] 0) Filter.atTop := by
    have h_eq : (fun y => (Real.log base - Real.log y) / L) =
                (fun y => (1 / L) * (-Real.log y) + Real.log base / L) := by ext; ring
    rw [h_eq]
    exact (Filter.Tendsto.const_mul_atTop (one_div_pos.mpr hL_pos)
      (Filter.tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero)).atTop_add tendsto_const_nhds
  have h_bound : ∀ᶠ y in 𝓝[>] 0, (Real.log base - Real.log y) / L ≤
      ∫ x in y..base, 1 / α.toFun x := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hbase.1)]
      with y hy_pos hy_lt_base
    have hx_pos : ∀ x ∈ Set.uIcc y base, 0 < x :=
      fun x hx => (lt_min hy_pos hbase.1).trans_le hx.1
    have hα_pos : ∀ x ∈ Set.Icc y base, 0 < α.toFun x := fun x hx =>
      α.pos_on_Ioo ⟨hy_pos.trans_le hx.1, hx.2.trans_lt hbase.2⟩
    have h1_intble : IntervalIntegrable (fun x => 1 / (L * x)) MeasureTheory.volume y base :=
      (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
        (fun x hx => (mul_pos hL_pos (hx_pos x hx)).ne')).intervalIntegrable
    calc (Real.log base - Real.log y) / L
        = ∫ x in y..base, 1 / (L * x) := by
            have h_deriv : ∀ x ∈ Set.uIcc y base,
                HasDerivAt (fun t => Real.log t / L) (1 / (L * x)) x := fun x hx => by
              have h := (Real.hasDerivAt_log (hx_pos x hx).ne').div_const L
              rwa [show x⁻¹ / L = 1 / (L * x) from by rw [inv_eq_one_div]; ring] at h
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h1_intble]; ring
      _ ≤ ∫ x in y..base, 1 / α.toFun x :=
            intervalIntegral.integral_mono_on hy_lt_base.le h1_intble
              ((continuousOn_const.div
                (α.continuous.mono fun x hx => by
                  rw [Set.uIcc_of_le hy_lt_base.le] at hx
                  exact ⟨hy_pos.le.trans hx.1, hx.2.trans_lt hbase.2⟩)
                fun x hx => by
                  rw [Set.uIcc_of_le hy_lt_base.le] at hx
                  exact (hα_pos x hx).ne').intervalIntegrable)
              fun x hx => div_le_div_of_nonneg_left zero_le_one (hα_pos x hx)
                (h_lin x ⟨hy_pos.trans_le hx.1, hx.2⟩)
  exact tendsto_atTop_mono' _ (h_bound.mono fun y hy => by
    change (Real.log base - Real.log y) / L ≤ -∫ x in base..y, 1 / α.toFun x
    rwa [intervalIntegral.integral_symm, neg_neg]) h_tendsto_log


/-! ### The σ function is Class KL -/

/-- **Osgood construction:** given `α : ClassK a b` satisfying the Osgood condition
    (`EtaDiverges`), `σ(r, s) = η⁻¹(η(r) + s)` extended by `σ(0, s) = 0` is Class KL. -/
@[blueprint "thm:class-KL-osgood"
  (statement := /-- \textbf{Osgood construction.}
    Given a class $\mathcal{K}$ function $\alpha$ satisfying the Osgood condition
    $\int_0^{\varepsilon} \frac{1}{\alpha(x)}\,dx = +\infty$,
    the function $\sigma(r, s) = \eta^{-1}(\eta(r) + s)$, where
    $\eta(y) = -\int_{\mathrm{base}}^{y} \frac{1}{\alpha(x)}\,dx$,
    is a class $\mathcal{KL}$ function (\cref{def:isClassKL}). -/)]
theorem ClassK.sigma_isClassKL (α : ClassK a b) (base : ℝ)
    (hbase : base ∈ Set.Ioo 0 a)
    (L : ℝ) (hL_pos : 0 < L)
    (hLip : ∀ x ∈ Set.Ioc 0 base, α.toFun x ≤ L * x) :
    ∃ σ : ClassKL a,
      (∀ r ∈ Set.Ioo 0 a, ∀ s ≥ 0, σ.toFun r s = α.sigma base r s) ∧
      (∀ s ≥ 0, σ.toFun 0 s = 0) := by
    have hdiv : α.EtaDiverges base :=
      ClassK.etaDiverges_of_le_linear α base hbase L hL_pos hLip
    refine ⟨{
      ha           := α.ha
      toFun        := α.sigma base
      -- σ(0, s) = 0 by definition
      map_zero     := fun s _ => by simp [ClassK.sigma]
      -- Continuity at r=0 needs etaInv_tendsto_zero; interior is composition of continuous fns
      continuous := by
        rintro ⟨r, s⟩ ⟨hr, hs⟩
        change ContinuousWithinAt (fun p : ℝ × ℝ => α.sigma base p.1 p.2)
            (Set.Ico 0 a ×ˢ Set.Ici 0) (r, s)
        simp only [ClassK.sigma]
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · -- r = 0: squeeze 0 ≤ σ(p) ≤ p.1 → 0
          simp only [ContinuousWithinAt]
          apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
              continuous_fst.continuousWithinAt
          · -- lower: 0 ≤ f(p) on domain
            filter_upwards [self_mem_nhdsWithin] with ⟨r', s'⟩ hp
            simp only [Set.mem_prod, Set.mem_Ico, Set.mem_Ici] at hp
            split_ifs with h
            · exact le_refl 0
            · exact (etaInv_mem_Ioo α base
                  (eta_add_mem_range α base hbase hdiv
                    ⟨lt_of_le_of_ne hp.1.1 (Ne.symm h), hp.1.2⟩ hp.2)).1.le
          · -- upper: f(p) ≤ p.1 on domain
            filter_upwards [self_mem_nhdsWithin] with ⟨r', s'⟩ hp
            simp only [Set.mem_prod, Set.mem_Ico, Set.mem_Ici] at hp
            split_ifs with h
            · exact hp.1.1
            · have hr'_pos : 0 < r' := lt_of_le_of_ne hp.1.1 (Ne.symm h)
              rcases eq_or_lt_of_le hp.2 with rfl | hs'_pos
              · simp [etaInv_eta α base hbase ⟨hr'_pos, hp.1.2⟩]
              · exact le_of_lt ((etaInv_strictAntiOn α base hbase
                    ⟨r', ⟨hr'_pos, hp.1.2⟩, rfl⟩
                    (eta_add_mem_range α base hbase hdiv ⟨hr'_pos, hp.1.2⟩ hs'_pos.le)
                    (by linarith)).trans_eq
                    (etaInv_eta α base hbase ⟨hr'_pos, hp.1.2⟩))
        · -- r > 0: etaInv(eta(·) + ·) is jointly continuous at (r, s)
          apply ContinuousAt.continuousWithinAt
          have heta_sum : ContinuousAt (fun p : ℝ × ℝ => α.eta base p.1 + p.2) (r, s) :=
            ((eta_hasDerivAt α base hbase ⟨hr_pos, hr.2⟩).continuousAt.comp
              continuousAt_fst).add continuousAt_snd
          have hetaInv : ContinuousAt (α.etaInv base)
              ((fun p : ℝ × ℝ => α.eta base p.1 + p.2) (r, s)) :=
            etaInv_continuousAt α base hbase
              (eta_add_mem_range α base hbase hdiv ⟨hr_pos, hr.2⟩ hs)
          have h_comp : ContinuousAt
            (fun p : ℝ × ℝ => α.etaInv base (α.eta base p.1 + p.2)) (r, s) :=
            ContinuousAt.comp (f := fun p : ℝ × ℝ => α.eta base p.1 + p.2) hetaInv heta_sum
          have h_eq : (fun p : ℝ × ℝ => α.etaInv base (α.eta base p.1 + p.2)) =ᶠ[𝓝 (r, s)]
              (fun p => if p.1 = 0 then 0 else α.etaInv base (α.eta base p.1 + p.2)) := by
            filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
                (Ioi_mem_nhds hr_pos)] with p hp
            exact (if_neg (Set.mem_Ioi.mp hp).ne').symm
          exact h_comp.congr h_eq

      -- σ strictly increasing in r: two cases
      strict_mono_r := fun s hs => by
        intro r₁ hr₁ r₂ hr₂ hr_lt
        rcases eq_or_lt_of_le hr₁.1 with rfl | hr₁_pos
        · -- r₁ = 0: σ(0,s) = 0, and σ(r₂,s) = etaInv(...) > 0
          simp only [ClassK.sigma, if_true, if_neg hr_lt.ne']
          exact (etaInv_mem_Ioo α base
            (eta_add_mem_range α base hbase hdiv ⟨hr_lt, hr₂.2⟩ hs)).1
        · -- 0 < r₁ < r₂: eta anti-mono gives eta(r₁)+s > eta(r₂)+s,
          --               then etaInv anti-mono flips back
          have hr₂_pos : (0 : ℝ) < r₂ := lt_trans hr₁_pos hr_lt
          simp only [ClassK.sigma, if_neg hr₁_pos.ne', if_neg hr₂_pos.ne']
          apply etaInv_strictAntiOn α base hbase
          · exact eta_add_mem_range α base hbase hdiv ⟨hr₂_pos, hr₂.2⟩ hs
          · exact eta_add_mem_range α base hbase hdiv ⟨hr₁_pos, hr₁.2⟩ hs
          · linarith [eta_strictAntiOn α base hbase
              ⟨hr₁_pos, hr₁.2⟩ ⟨hr₂_pos, hr₂.2⟩ hr_lt]
      -- σ ≥ 0: either r=0 (trivial) or etaInv lands in Ioo 0 a
      nonneg := fun r hr s hs => by
        simp only [ClassK.sigma]
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · simp
        · rw [if_neg hr_pos.ne']
          exact le_of_lt (etaInv_mem_Ioo α base
            (eta_add_mem_range α base hbase hdiv ⟨hr_pos, hr.2⟩ hs)).1
      -- σ antitone in s: larger s → larger input to etaInv → smaller output
      anti_s := fun r hr => by
        intro s₁ hs₁ s₂ hs₂ hs_le
        simp only [ClassK.sigma]
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · simp
        · simp only [if_neg hr_pos.ne']
          rcases eq_or_lt_of_le hs_le with rfl | hs_lt
          · exact le_refl _
          · exact le_of_lt (etaInv_strictAntiOn α base hbase
              (eta_add_mem_range α base hbase hdiv ⟨hr_pos, hr.2⟩ hs₁)
              (eta_add_mem_range α base hbase hdiv ⟨hr_pos, hr.2⟩ hs₂)
              (by linarith))
      -- σ(r,s) → 0 as s → ∞: compose etaInv_tendsto_zero with (eta(r) + ·) → ∞
      tendsto_zero := fun r hr => by
        simp only [ClassK.sigma]
        rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
        · simp only; exact tendsto_const_nhds
        · simp only  [if_neg hr_pos.ne']
          exact (etaInv_tendsto_zero α base hbase).comp
            (tendsto_atTop_add_const_left _ (α.eta base r) tendsto_id)
    }, ⟨fun r _ s _ => rfl, fun s _ => by simp [ClassK.sigma]⟩⟩


lemma ClassK.sigma_hasDerivAt {a b : ℝ} (α : ClassK a b) (base : ℝ)
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


/-! ## Comparison bound from Dini ≤ −ClassK -/

/-- **Comparison KL bound**: for any class K function `α`, there exists a class KL function `σ`
    such that any continuous scalar function `v` with upper-right Dini derivative
    `D⁺v(s) ≤ −α(v(s))`, starting and remaining in `[0, a)`, satisfies
    `v(t) ≤ σ(v(t₀), t − t₀)`.

    The class K decay ODE `ẏ = −α(y)` determines σ; the comparison lemma supplies the
    bound. All ODE infrastructure (Lipschitz minorant, Osgood construction,
    Picard–Lindelöf) is hidden inside. -/
lemma classK_dini_bound {a b : ℝ} (α : ClassK a b) :
    ∃ σ : ClassKL a,
      (∀ r ∈ Set.Ico 0 a, σ.toFun r 0 ≤ r) ∧
      ∀ {t₀ t : ℝ}, t₀ ≤ t → ∀ (v : ℝ → ℝ), Continuous v →
        v t₀ ∈ Set.Ico 0 a →
        (∀ s ∈ Set.Ico t₀ t, v s ∈ Set.Ico 0 a) →
        (∀ s ∈ Set.Ico t₀ t, D⁺ v s ≤ -α.toFun (v s)) →
        (∀ s ∈ Set.Ico t₀ t,
            IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (s + h) - v s) / h)) →
        v t ≤ σ.toFun (v t₀) (t - t₀) := by
  obtain ⟨β, β_ext, L, hL_pos, hβ_le_α, hβ_ext_eq, hLip, hβ_ext_cont, hLip_ext⟩ :=
    exists_classK_minorant_lipschitz α (a / 2) ⟨half_pos α.ha, half_lt_self α.ha⟩
  obtain ⟨σ, hσ_eq, hσ_zero_s⟩ := ClassK.sigma_isClassKL β (a / 2)
    ⟨half_pos α.ha, half_lt_self α.ha⟩ L hL_pos hLip
  have h_base : a / 2 ∈ Set.Ioo 0 a := ⟨half_pos α.ha, half_lt_self α.ha⟩
  have h_sigma_zero_at : ∀ r ∈ Set.Ioo 0 a, β.sigma (a / 2) r 0 = r := fun r hr => by
    simp only [ClassK.sigma, if_neg hr.1.ne', add_zero]
    exact etaInv_eta β (a / 2) h_base hr
  refine ⟨σ, ?_, ?_⟩
  · -- σ(r, 0) ≤ r for r ∈ [0, a)
    intro r hr
    rcases eq_or_lt_of_le hr.1 with rfl | hr_pos
    · rw [hσ_zero_s 0 le_rfl]
    · have hr_Ioo : r ∈ Set.Ioo 0 a := ⟨hr_pos, hr.2⟩
      rw [hσ_eq r hr_Ioo 0 le_rfl, h_sigma_zero_at r hr_Ioo]
  · -- Trajectory bound
    intro t₀ t ht v hv_cont hv₀ hv_range hDv hv_bdd
    rcases eq_or_lt_of_le ht with rfl | ht_lt
    · simp only [sub_self]
      rcases eq_or_lt_of_le hv₀.1 with h_eq | hv_pos
      · simp [show v t₀ = 0 from h_eq.symm, hσ_zero_s 0 le_rfl]
      · rw [hσ_eq (v t₀) ⟨hv_pos, hv₀.2⟩ 0 le_rfl, h_sigma_zero_at (v t₀) ⟨hv_pos, hv₀.2⟩]
    · -- Strengthen: D⁺v ≤ -α(v) ≤ -β(v) = -β_ext(v)
      have hDv' : ∀ s ∈ Set.Ico t₀ t, D⁺ v s ≤ (fun _ x => -β_ext x) s (v s) := by
        intro s hs
        have hvs := hv_range s hs
        have h1 : D⁺ v s ≤ -α.toFun (v s) := hDv s hs
        have h2 : β.toFun (v s) ≤ α.toFun (v s) := hβ_le_α (v s) hvs
        have h3 : β_ext (v s) = β.toFun (v s) := hβ_ext_eq (v s) hvs
        linarith
      -- σ satisfies the comparison ODE u̇ = -β_ext(u)
      have hu_deriv : ∀ s ∈ Set.Ioo t₀ t,
          HasDerivAt (fun x => σ.toFun (v t₀) (x - t₀))
            ((fun _ x => -β_ext x) s (σ.toFun (v t₀) (s - t₀))) s := by
        intro s hs
        rcases eq_or_lt_of_le hv₀.1 with h_eq | hv_pos
        · -- v t₀ = 0: σ(0, ·) = 0 everywhere
          have hvt₀_zero : v t₀ = 0 := h_eq.symm
          rw [hvt₀_zero]
          have h_u_eq : (fun x => σ.toFun 0 (x - t₀)) =ᶠ[𝓝 s] (fun _ => 0) :=
            Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs.1) fun x hx =>
              hσ_zero_s (x - t₀) (sub_nonneg.mpr hx.le)
          have h_val : -β_ext (σ.toFun 0 (s - t₀)) = 0 := by
            rw [hσ_zero_s (s - t₀) (sub_nonneg.mpr hs.1.le),
                hβ_ext_eq 0 ⟨le_rfl, α.ha⟩, β.map_zero, neg_zero]
          have h_final := (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq h_u_eq
          change HasDerivAt (fun x => σ.toFun 0 (x - t₀)) (-β_ext (σ.toFun 0 (s - t₀))) s
          rwa [h_val]
        · -- v t₀ > 0: use sigma_hasDerivAt + chain rule
          have hv₀_Ioo : v t₀ ∈ Set.Ioo 0 a := ⟨hv_pos, hv₀.2⟩
          have hs_sub_pos : 0 < s - t₀ := sub_pos.mpr hs.1
          -- σ(v t₀, s - t₀) stays in [0, a)
          have h_sigma_ico : σ.toFun (v t₀) (s - t₀) ∈ Set.Ico 0 a := by
            refine ⟨σ.nonneg _ ⟨hv₀_Ioo.1.le, hv₀_Ioo.2⟩ _ hs_sub_pos.le, ?_⟩
            calc σ.toFun (v t₀) (s - t₀)
                ≤ σ.toFun (v t₀) 0 :=
                    σ.anti_s _ ⟨hv₀_Ioo.1.le, hv₀_Ioo.2⟩
                      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs_sub_pos.le) hs_sub_pos.le
              _ = β.sigma (a / 2) (v t₀) 0 := hσ_eq (v t₀) hv₀_Ioo 0 le_rfl
              _ = v t₀ := h_sigma_zero_at (v t₀) hv₀_Ioo
              _ < a := hv₀_Ioo.2
          -- β.sigma (a/2) (v t₀) (s - t₀) ∈ [0, a) (same value, rewritten form)
          have h_sigma_ico' : β.sigma (a / 2) (v t₀) (s - t₀) ∈ Set.Ico 0 a := by
            rw [← hσ_eq (v t₀) hv₀_Ioo (s - t₀) hs_sub_pos.le]; exact h_sigma_ico
          -- sigma_hasDerivAt + chain rule gives derivative of σ(v t₀, · - t₀) at s
          have h_base_deriv := ClassK.sigma_hasDerivAt β (a / 2) h_base L hL_pos hLip
            (v t₀) hv₀_Ioo (s - t₀) hs_sub_pos
          have h_comp := h_base_deriv.comp s ((hasDerivAt_id s).sub_const t₀)
          simp only [mul_one] at h_comp
          change HasDerivAt (fun x => β.sigma (a / 2) (v t₀) (x - t₀))
            (-β.toFun (β.sigma (a / 2) (v t₀) (s - t₀))) s at h_comp
          -- Rewrite β.sigma to σ.toFun via hσ_eq
          have h_func_eq : (fun x => β.sigma (a / 2) (v t₀) (x - t₀)) =ᶠ[𝓝 s]
              (fun x => σ.toFun (v t₀) (x - t₀)) :=
            Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs.1) fun x hx =>
              (hσ_eq (v t₀) hv₀_Ioo (x - t₀) (sub_nonneg.mpr hx.le)).symm
          -- Match derivative value: -β.toFun (β.sigma ...) = -β_ext (σ.toFun ...)
          have h_val : -β.toFun (β.sigma (a / 2) (v t₀) (s - t₀)) =
              -β_ext (σ.toFun (v t₀) (s - t₀)) := by
            conv_rhs => rw [hσ_eq (v t₀) hv₀_Ioo (s - t₀) hs_sub_pos.le]
            rw [hβ_ext_eq _ h_sigma_ico']
          have h_final := h_comp.congr_of_eventuallyEq h_func_eq.symm
          rwa [h_val] at h_final
      -- σ is continuous on [t₀, t]
      have hu_cont : ContinuousOn (fun s => σ.toFun (v t₀) (s - t₀)) (Set.Icc t₀ t) :=
        (σ.continuous.comp
          (continuousOn_const.prodMk (continuousOn_id.sub continuousOn_const))
          (fun s hs => ⟨hv₀, Set.mem_Ici.mpr (sub_nonneg.mpr hs.1)⟩)).congr
          (fun s _ => rfl)
      -- σ(v t₀, 0) = v t₀ (initial condition)
      have hu₀ : (fun s => σ.toFun (v t₀) (s - t₀)) t₀ = v t₀ := by
        simp only [sub_self]
        rcases eq_or_lt_of_le hv₀.1 with h_eq | hv_pos
        · rw [show v t₀ = 0 from h_eq.symm]; exact hσ_zero_s 0 le_rfl
        · rw [hσ_eq (v t₀) ⟨hv_pos, hv₀.2⟩ 0 le_rfl, h_sigma_zero_at (v t₀) ⟨hv_pos, hv₀.2⟩]
      -- Apply comparison_lemma
      have h_bound : ∀ s ∈ Set.Icc t₀ t, v s ≤ σ.toFun (v t₀) (s - t₀) :=
        comparison_lemma (f := fun _ x => -β_ext x) ht_lt hL_pos
          ((hβ_ext_cont.neg.comp continuous_snd))
          (fun _ _ => hLip_ext.neg)
          hu_deriv hu_cont hu₀
          hv_cont hDv' hv_bdd le_rfl
          (fun lam hlam => by
            have hg_cont : Continuous (Function.uncurry (fun (_ : ℝ) x => -β_ext x + lam)) :=
              (hβ_ext_cont.neg.add continuous_const).comp continuous_snd
            have hg_lip : ∀ _ : ℝ, LipschitzWith ⟨L, hL_pos.le⟩ (fun x => -β_ext x + lam) :=
              fun _ x y => by
                have h_edist : edist (-β_ext x + lam) (-β_ext y + lam) =
                    edist (β_ext x) (β_ext y) := by
                  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]; congr 1
                  calc ‖-β_ext x + lam - (-β_ext y + lam)‖
                      = ‖-(β_ext x - β_ext y)‖ := by congr 1; ring
                    _ = ‖β_ext x - β_ext y‖    := norm_neg _
                rw [h_edist]; exact hLip_ext x y
            exact scalar_ode_exists_interval (fun _ x => -β_ext x + lam) L hL_pos
              hg_cont hg_lip ht_lt.le)
      exact h_bound t ⟨ht_lt.le, le_rfl⟩
