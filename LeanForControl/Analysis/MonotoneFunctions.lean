import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue


import Architect

open MeasureTheory intervalIntegral Set Filter Topology

/-! ## Antitone function inverses -/

/-- A continuous function `W : ℝ → ℝ` on `(0, ∞)` that tends to `+∞` near `0⁺` and to `0`
    at `+∞` surjects onto `(0, ∞)`: every `s > 0` lies in the image `W '' (Ioi 0)`. -/
@[blueprint "lem:memImageIoiOfTendsto"
  (title := "Surjectivity onto $(0,\\infty)$ from the two boundary limits")
  (latexEnv := "lemma")
  (statement := /-- Let $W : \mathbb{R} \to \mathbb{R}$ be continuous on $(0,\infty)$ with
    $W(\eta) \to +\infty$ as $\eta \to 0^+$ and $W(\eta) \to 0$ as $\eta \to +\infty$.
    Then for every $s > 0$ there exists $c > 0$ with $W(c) = s$. -/)]
lemma mem_image_Ioi_of_tendsto {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    (hW_tendsto_top : Filter.Tendsto W (𝓝[>] 0) Filter.atTop)
    {s : ℝ} (hs : 0 < s) :
    s ∈ W '' Set.Ioi 0 := by
  -- Step 1: Find a large b > 0 where W(b) < s
  have hb_full : ∀ᶠ x in Filter.atTop, 0 < x ∧ W x < s := by
    filter_upwards [Filter.eventually_gt_atTop 0, hW_tendsto_zero (gt_mem_nhds hs)]
      with x hx1 hx2 using ⟨hx1, hx2⟩
  obtain ⟨b, hb_pos, hb_lt⟩ := hb_full.exists
  -- Step 2: Find a small a ∈ (0, b) where W(a) > s
  have ha_full : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ x < b ∧ s < W x := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hb_pos),
      hW_tendsto_top (Filter.Ioi_mem_atTop s)] with x h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨a, ha_pos, ha_lt_b, ha_gt⟩ := ha_full.exists
  -- Step 3: Apply IVT to -W on [a, b]
  have h_cont_neg : ContinuousOn (fun x => -W x) (Set.Icc a b) :=
    (hW_cont.mono fun _ hx => ha_pos.trans_le hx.1).neg
  obtain ⟨c, hc_Icc, hc_eq⟩ := intermediate_value_Icc ha_lt_b.le h_cont_neg
    ⟨neg_le_neg ha_gt.le, neg_le_neg hb_lt.le⟩
  exact ⟨c, ha_pos.trans_le hc_Icc.1, by linarith⟩


/-- The canonical right inverse `invFunOn W (Ioi 0)` satisfies `W(invFunOn W (Ioi 0) s) = s`
    for every `s > 0`, given the surjectivity conditions. -/
@[blueprint "lem:applyInvFunOnEq"
  (title := "The right inverse inverts")
  (latexEnv := "lemma")
  (statement := /-- Under the surjectivity conditions of \cref{lem:memImageIoiOfTendsto},
    $W\bigl(\mathrm{invFunOn}\,W\,(0,\infty)\,s\bigr) = s$ for all $s > 0$. -/)]
lemma apply_invFunOn_eq {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    (hW_tendsto_top : Filter.Tendsto W (𝓝[>] 0) Filter.atTop)
    {s : ℝ} (hs : 0 < s) :
    W (Function.invFunOn W (Set.Ioi 0) s) = s :=
  Function.invFunOn_eq (mem_image_Ioi_of_tendsto hW_cont hW_tendsto_zero hW_tendsto_top hs)


/-- The canonical right inverse `invFunOn W (Ioi 0) s` is positive for every `s > 0`. -/
@[blueprint "lem:invFunOnPos"
  (title := "Positivity of the right inverse")
  (latexEnv := "lemma")
  (statement := /-- Under the surjectivity conditions of \cref{lem:memImageIoiOfTendsto},
    $\mathrm{invFunOn}\,W\,(0,\infty)\,s > 0$ for all $s > 0$. -/)]
lemma invFunOn_pos {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    (hW_tendsto_top : Filter.Tendsto W (𝓝[>] 0) Filter.atTop)
    {s : ℝ} (hs : 0 < s) :
    0 < Function.invFunOn W (Set.Ioi 0) s :=
  Function.invFunOn_mem (mem_image_Ioi_of_tendsto hW_cont hW_tendsto_zero hW_tendsto_top hs)


/-- If `W` is strictly antitone on `(0, ∞)`, then so is its right inverse
    `invFunOn W (Ioi 0)`. -/
@[blueprint "lem:strictAntiOnInvFunOn"
  (title := "The inverse of a strictly antitone function is strictly antitone")
  (latexEnv := "lemma")
  (statement := /-- If $W$ is strictly antitone on $(0,\infty)$, then
    $\mathrm{invFunOn}\,W\,(0,\infty)$ is strictly antitone on $(0,\infty)$. -/)]
lemma strictAntiOn_invFunOn {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Ioi 0))
    (hW_anti : StrictAntiOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    (hW_tendsto_top : Filter.Tendsto W (𝓝[>] 0) Filter.atTop) :
    StrictAntiOn (Function.invFunOn W (Set.Ioi 0)) (Set.Ioi 0) := by
  intro s₁ hs₁ s₂ hs₂ h_lt
  by_contra h_contra
  push Not at h_contra
  set U₁ := Function.invFunOn W (Set.Ioi 0) s₁
  set U₂ := Function.invFunOn W (Set.Ioi 0) s₂
  have hU₁_pos : 0 < U₁ :=
    Function.invFunOn_mem (mem_image_Ioi_of_tendsto hW_cont hW_tendsto_zero hW_tendsto_top hs₁)
  have hU₂_pos : 0 < U₂ :=
    Function.invFunOn_mem (mem_image_Ioi_of_tendsto hW_cont hW_tendsto_zero hW_tendsto_top hs₂)
  have hW₁ : W U₁ = s₁ := apply_invFunOn_eq hW_cont hW_tendsto_zero hW_tendsto_top hs₁
  have hW₂ : W U₂ = s₂ := apply_invFunOn_eq hW_cont hW_tendsto_zero hW_tendsto_top hs₂
  rcases h_contra.lt_or_eq with h_U_lt | h_U_eq
  · have hW_lt : W U₂ < W U₁ := hW_anti hU₁_pos hU₂_pos h_U_lt
    rw [hW₁, hW₂] at hW_lt; linarith
  · have hW_eq : W U₁ = W U₂ := congr_arg W h_U_eq
    rw [hW₁, hW₂] at hW_eq; linarith

/-- The right inverse `invFunOn W (Ioi 0)` tends to `0` as `s → +∞`, provided `W` satisfies
    the standard boundary conditions. -/
@[blueprint "lem:invFunOnTendstoZero"
  (title := "The inverse vanishes at $+\\infty$")
  (latexEnv := "lemma")
  (statement := /-- Under the conditions of \cref{lem:memImageIoiOfTendsto} and with $W$
    strictly antitone, $\mathrm{invFunOn}\,W\,(0,\infty)\,s \to 0$ as $s \to +\infty$. -/)]
lemma invFunOn_tendsto_zero {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Ioi 0))
    (hW_anti : StrictAntiOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    (hW_tendsto_top : Filter.Tendsto W (𝓝[>] 0) Filter.atTop) :
    Filter.Tendsto (Function.invFunOn W (Set.Ioi 0)) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- N = max (W ε) 0 + 1 ensures N > W(ε) and N > 0
  refine ⟨max (W ε) 0 + 1, fun s hs => ?_⟩
  have hs_pos : 0 < s := by linarith [le_max_right (W ε) 0]
  set U_s := Function.invFunOn W (Set.Ioi 0) s
  have hU_pos : 0 < U_s :=
    Function.invFunOn_mem (mem_image_Ioi_of_tendsto hW_cont hW_tendsto_zero hW_tendsto_top hs_pos)
  have hW_U : W U_s = s := apply_invFunOn_eq hW_cont hW_tendsto_zero hW_tendsto_top hs_pos
  have hs_gt_Wε : W ε < W U_s := by rw [hW_U]; linarith [le_max_left (W ε) 0]
  -- Prove U_s < ε by contradiction
  have hU_lt_ε : U_s < ε := by
    by_contra h_contra
    push Not at h_contra
    rcases h_contra.lt_or_eq with h_lt | h_eq
    · linarith [hW_anti hε hU_pos h_lt]
    · rw [h_eq] at hs_gt_Wε; linarith
  rw [Real.dist_eq, sub_zero, abs_of_pos hU_pos]
  exact hU_lt_ε


/-- A strictly antitone function on `(0, ∞)` that vanishes at `+∞` is strictly positive: it
    stays above its own limit. -/
private lemma pos_of_strictAntiOn_tendsto_zero {W : ℝ → ℝ}
    (hW_anti : StrictAntiOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    {x : ℝ} (hx : 0 < x) :
    0 < W x := by
  have h_nonneg : ∀ y, 0 < y → 0 ≤ W y := fun y hy =>
    le_of_tendsto hW_tendsto_zero <| by
      filter_upwards [Filter.eventually_ge_atTop y] with z hz
      exact hW_anti.antitoneOn hy (hy.trans_le hz) hz
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have : W (x + 1) < W x := hW_anti (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hx1) (by linarith)
  linarith [h_nonneg (x + 1) hx1]


/-- The right inverse `invFunOn W (Ioi 0)` is continuous on `(0, ∞)`.

Order-theoretic, not analytic: the inverse of a strictly antitone map has no jumps precisely
because `W` attains every positive value (`mem_image_Ioi_of_tendsto`), so both one-sided
comparisons in `tendsto_order` can be met by transporting them through `W`. -/
@[blueprint "lem:invFunOnContinuousOn"
  (title := "Continuity of the inverse")
  (latexEnv := "lemma")
  (statement := /-- Under the conditions of \cref{lem:memImageIoiOfTendsto} and with $W$
    strictly antitone, $\mathrm{invFunOn}\,W\,(0,\infty)$ is continuous on $(0,\infty)$. -/)]
lemma invFunOn_continuousOn {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Ioi 0))
    (hW_anti : StrictAntiOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    (hW_tendsto_top : Filter.Tendsto W (𝓝[>] 0) Filter.atTop) :
    ContinuousOn (Function.invFunOn W (Set.Ioi 0)) (Set.Ioi 0) := by
  have hpos : ∀ {s : ℝ}, 0 < s → 0 < Function.invFunOn W (Set.Ioi 0) s := fun hs =>
    invFunOn_pos hW_cont hW_tendsto_zero hW_tendsto_top hs
  have heq : ∀ {s : ℝ}, 0 < s → W (Function.invFunOn W (Set.Ioi 0) s) = s := fun hs =>
    apply_invFunOn_eq hW_cont hW_tendsto_zero hW_tendsto_top hs
  intro s₀ hs₀
  apply ContinuousAt.continuousWithinAt
  rw [ContinuousAt, tendsto_order]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · -- `z < invFunOn W _ s₀`: either `z ≤ 0`, where positivity alone suffices, or `z > 0` and
    -- the comparison transports to `s₀ < W z`, which is an open condition on `s`.
    rcases le_or_gt z 0 with hz0 | hz0
    · filter_upwards [Ioi_mem_nhds hs₀] with s hs using hz0.trans_lt (hpos hs)
    · have h_gt : s₀ < W z := by rw [← heq hs₀]; exact hW_anti hz0 (hpos hs₀) hz
      filter_upwards [Iio_mem_nhds h_gt, Ioi_mem_nhds hs₀] with s hs_lt hs_pos
      by_contra h_le
      push Not at h_le
      have := hW_anti.antitoneOn (Set.mem_Ioi.mpr (hpos hs_pos)) (Set.mem_Ioi.mpr hz0) h_le
      rw [heq hs_pos] at this
      exact absurd this (not_le.mpr hs_lt)
  · have hz_pos : 0 < z := (hpos hs₀).trans hz
    have h_lt : W z < s₀ := by rw [← heq hs₀]; exact hW_anti (hpos hs₀) hz_pos hz
    filter_upwards [Ioi_mem_nhds h_lt, Ioi_mem_nhds hs₀] with s hs_gt hs_pos
    by_contra h_ge
    push Not at h_ge
    have := hW_anti.antitoneOn (Set.mem_Ioi.mpr hz_pos) (Set.mem_Ioi.mpr (hpos hs_pos)) h_ge
    rw [heq hs_pos] at this
    exact absurd this (not_le.mpr hs_gt)


/-- The right inverse `invFunOn W (Ioi 0)` blows up as `s → 0⁺`: the two boundary behaviours of
    `W` are exchanged by inversion. -/
@[blueprint "lem:invFunOnTendstoAtTop"
  (title := "The inverse blows up at $0^{+}$")
  (latexEnv := "lemma")
  (statement := /-- Under the conditions of \cref{lem:memImageIoiOfTendsto} and with $W$
    strictly antitone, $\mathrm{invFunOn}\,W\,(0,\infty)\,s \to +\infty$ as $s \to 0^{+}$. -/)]
lemma invFunOn_tendsto_atTop {W : ℝ → ℝ}
    (hW_cont : ContinuousOn W (Set.Ioi 0))
    (hW_anti : StrictAntiOn W (Set.Ioi 0))
    (hW_tendsto_zero : Filter.Tendsto W Filter.atTop (nhds 0))
    (hW_tendsto_top : Filter.Tendsto W (𝓝[>] 0) Filter.atTop) :
    Filter.Tendsto (Function.invFunOn W (Set.Ioi 0)) (𝓝[>] 0) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rcases le_or_gt b 0 with hb | hb
  · filter_upwards [self_mem_nhdsWithin] with s hs_pos
    exact hb.trans (invFunOn_pos hW_cont hW_tendsto_zero hW_tendsto_top hs_pos).le
  · -- For `s` below the threshold `W b > 0`, antitonicity forces `invFunOn W _ s ≥ b`.
    have hWb_pos : 0 < W b := pos_of_strictAntiOn_tendsto_zero hW_anti hW_tendsto_zero hb
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hWb_pos)] with s hs_pos hs_lt
    by_contra h_le
    push Not at h_le
    have := hW_anti.antitoneOn
      (Set.mem_Ioi.mpr (invFunOn_pos hW_cont hW_tendsto_zero hW_tendsto_top hs_pos))
      (Set.mem_Ioi.mpr hb) h_le.le
    rw [apply_invFunOn_eq hW_cont hW_tendsto_zero hW_tendsto_top hs_pos] at this
    exact absurd this (not_le.mpr hs_lt)

/-! ## Continuous strictly monotone bounds

A Lyapunov function's sublevel data gives only *monotone* bounds; the comparison-function
machinery needs *strictly* monotone continuous ones. These say the gap can always be closed, in
either direction.

* The lower (minorant) direction integrates: `r⁻¹ ∫₀ˢ ψ`.
* The upper (majorant) direction averages: `s + ⨍_{[s, 2s]} φ`. It needs `φ` to be continuous at
  `0`, since a continuous majorant vanishing at `0` cannot sit above a jump there.
-/

/-- A monotonically non-decreasing positive function can be lower-bounded by a strictly monotonic
continuous function. -/
@[blueprint "lem:exists-strictMono-lower-bound"
  (title := "Class $\\mathcal{K}$ minorant of a positive monotone function") (latexEnv := "lemma")
  (statement := /-- Let $r > 0$ and let $\psi : \mathbb{R} \to \mathbb{R}$ satisfy
    $\psi(0) = 0$, $\psi(s) > 0$ for $s \in (0, r]$, and $\psi$ nondecreasing on $[0, r]$.
    Then there are $b > 0$ and a function $f$ with $f(0) = 0$, $f(r) = b$, $f$ continuous and
    strictly increasing on $[0, r]$, and $f(s) \le \psi(s)$ for all $s \in [0, r]$.

    That is: a positive nondecreasing function admits a class $\mathcal{K}$ minorant on any
    bounded interval.  This is what turns a positive-definite $V$ into the lower comparison
    bound of \cref{thm:lyapunov-class-K-bounds}. -/)
  (proof := /-- Take $f(s) = r^{-1} \int_0^s \psi$ (with the argument of $\psi$ clamped to
    $[0, r]$, so that it is monotone, hence integrable, on all of $\mathbb{R}$).  It is
    continuous as a primitive, and $f(0) = 0$.  For $s < s'$ in $[0, r]$,
    $f(s') - f(s) = r^{-1} \int_s^{s'} \psi > 0$ since $\psi > 0$ on $(s, s')$, so $f$ is
    strictly increasing and $b = f(r) > 0$.  Finally, $\psi$ is nondecreasing, so
    $\int_0^s \psi \le s\,\psi(s) \le r\,\psi(s)$, i.e.\ $f(s) \le \psi(s)$. -/)]
theorem exists_strictMono_lower_bound (r : ℝ) (hr : 0 < r) (ψ : ℝ → ℝ)
    (hψ_zero : ψ 0 = 0)
    (hψ_pos : ∀ s, 0 < s → s ≤ r → 0 < ψ s)
    (hψ_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ r → ψ s₁ ≤ ψ s₂) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → f s ≤ ψ s := by
  /- We take `f s = r⁻¹ ∫₀ˢ ψ`.  Since `ψ` is nondecreasing, `∫₀ˢ ψ ≤ s ψ(s) ≤ r ψ(s)`, so
     `f ≤ ψ`; since `ψ > 0` away from `0`, `f` is strictly increasing. -/
  -- Step 1. Clamp the argument to `[0, r]`, so that `χ` is monotone (hence integrable) on all
  -- of `ℝ`.
  set χ : ℝ → ℝ := fun t => ψ (max (min t r) 0)
  have hχ_mono : Monotone χ := fun x y h =>
    hψ_mono _ _ (le_max_right _ 0) (max_le_max (min_le_min h le_rfl) le_rfl)
      (max_le (min_le_right y r) hr.le)
  have hχ_eq : ∀ s, 0 ≤ s → s ≤ r → χ s = ψ s := fun s hs hsr => by
    simp [χ, min_eq_left hsr, max_eq_left hs]
  have hχ_pos : ∀ t > 0, 0 < χ t := fun t ht =>
    hψ_pos _ (lt_max_of_lt_left (lt_min ht hr)) (max_le (min_le_right t r) hr.le)
  have hχ_int : ∀ a b, IntervalIntegrable χ volume a b := fun _ _ =>
    hχ_mono.intervalIntegrable
  -- Step 2. The normalised primitive `f s = r⁻¹ ∫₀ˢ χ`.
  set f : ℝ → ℝ := fun s => r⁻¹ * ∫ x in (0 : ℝ)..s, χ x
  have hf_zero : f 0 = 0 := by simp [f]
  have hf_cont : Continuous f :=
    continuous_const.mul (intervalIntegral.continuous_primitive hχ_int 0)
  -- Strictly increasing: `f s' - f s = r⁻¹ ∫ₛ^{s'} χ`, and `χ > 0` on `(s, s')`.
  have hf_mono : StrictMonoOn f (Icc 0 r) := by
    intro s hs s' _ hss'
    have h_pos : 0 < ∫ x in s..s', χ x :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hχ_int _ _)
        (fun x hx => hχ_pos x (hs.1.trans_lt hx.1)) hss'
    rw [← intervalIntegral.integral_interval_sub_left (hχ_int 0 s') (hχ_int 0 s)] at h_pos
    exact mul_lt_mul_of_pos_left (sub_pos.mp h_pos) (inv_pos.mpr hr)
  -- Below `ψ`: `∫₀ˢ χ ≤ ∫₀ˢ χ(s) = s ψ(s) ≤ r ψ(s)`, because `χ` is nondecreasing.
  have hf_le : ∀ s, 0 ≤ s → s ≤ r → f s ≤ ψ s := fun s hs hsr => by
    have h_int : ∫ x in (0 : ℝ)..s, χ x ≤ s * ψ s := by
      have h := intervalIntegral.integral_mono_on hs (hχ_int 0 s)
        intervalIntegral.intervalIntegrable_const fun x hx => hχ_mono hx.2
      simpa [hχ_eq s hs hsr] using h
    have h_nonneg : 0 ≤ ψ s := hψ_zero ▸ hψ_mono 0 s le_rfl hs hsr
    rw [inv_mul_le_iff₀ hr]
    exact h_int.trans (mul_le_mul_of_nonneg_right hsr h_nonneg)
  -- Step 3. Take `b = f r`, which is positive because `f` increases from `f 0 = 0`.
  refine ⟨f, f r, ?_, hf_zero, rfl, hf_cont.continuousOn, hf_mono, hf_le⟩
  exact hf_zero ▸ hf_mono (left_mem_Icc.mpr hr.le) (right_mem_Icc.mpr hr.le) hr


/-- A monotonically non-decreasing function on `[0, ∞)` that is continuous at `0` with value `0`
    can be upper-bounded by a strictly monotonic continuous function that tends to `+∞`.

The continuity hypothesis cannot be dropped: the unit step (`0` at `0`, `1` after) has no
continuous majorant vanishing at `0`. -/
@[blueprint "lem:exists-strictMono-upper-bound-global"
  (title := "Class $\\mathcal{K}_{\\infty}$ majorant of a monotone function") (latexEnv := "lemma")
  (statement := /-- Let $\varphi : \mathbb{R} \to \mathbb{R}$ satisfy $\varphi(0) = 0$, be
    monotone on $[0, \infty)$, and be continuous at $0$ from the right.  Then there is an
    $f$ with $f(0) = 0$, continuous and strictly increasing on $[0, \infty)$,
    $f(s) \to \infty$ as $s \to \infty$, and $\varphi(s) \le f(s)$ for all $s \ge 0$.

    That is: a nondecreasing function admits a class $\mathcal{K}_{\infty}$ majorant.  The
    unbounded domain is what distinguishes this from
    \cref{lem:exists-strictMono-upper-bound}, which it implies.

    Continuity at $0$ is necessary: the unit step has no continuous majorant vanishing at
    $0$. -/)
  (proof := /-- Take $f(s) = s + g(s)$ with $g(s) = \int_1^2 \varphi(su)\,du$, the average of
    $\varphi$ over $[s, 2s]$ (with $\varphi$ clamped to $\varphi(\max(t,0))$ so that it is
    monotone, hence integrable, on all of $\mathbb{R}$).  Monotonicity of $\varphi$ gives
    $\varphi(s) \le g(s) \le \varphi(2s)$ and that $g$ is nondecreasing, so $f$ is strictly
    increasing, $f \ge \varphi$, and $f(s) \ge s \to \infty$.  For $s > 0$,
    $g(s) = s^{-1}\bigl(\Phi(2s) - \Phi(s)\bigr)$ with $\Phi$ the (continuous) primitive of
    $\varphi$, so $g$ is continuous there; at $0$, $0 \le g(s) \le \varphi(2s) \to 0$ by
    continuity of $\varphi$ at $0$. -/)]
theorem exists_strictMono_upper_bound_global (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Ici 0))
    (hφ_cont : ContinuousWithinAt φ (Set.Ici 0) 0) :
    ∃ f : ℝ → ℝ,
      f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      StrictMonoOn f (Set.Ici 0) ∧
      Filter.Tendsto f Filter.atTop Filter.atTop ∧
      ∀ s ≥ 0, φ s ≤ f s := by
  /- We take `f s = s + g s`, where `g s` is the average of `φ` over `[s, 2s]`.
     The window lies to the right of `s`, so `g ≥ φ`; it shrinks to `0` with `s`, so `g`
     inherits continuity at `0` from `φ`; and the `s` term makes `f` strictly increasing. -/

  -- Step 1. Clamp the argument at `0`, so that `ψ` is monotone (hence integrable) on all of `ℝ`.
  set ψ : ℝ → ℝ := fun t => φ (max t 0)
  have hψ_mono : Monotone ψ := fun x y h =>
    hφ_mono (le_max_right x 0) (le_max_right y 0) (max_le_max h le_rfl)
  have hψ_eq : ∀ s ≥ 0, ψ s = φ s := fun s hs => by simp [ψ, max_eq_left hs]
  have hψ_nonneg : ∀ t, 0 ≤ ψ t := fun t =>
    hφ_zero ▸ hφ_mono (le_refl (0 : ℝ)) (le_max_right t 0) (le_max_right t 0)
  have hψ_int : ∀ a b, IntervalIntegrable ψ volume a b := fun _ _ =>
    hψ_mono.intervalIntegrable
  -- Step 2. The average `g s = ∫₁² ψ(s u) du` of `ψ` over `[s, 2s]`.
  set g : ℝ → ℝ := fun s => ∫ u in (1 : ℝ)..2, ψ (s * u)
  have hg_int : ∀ s ≥ 0, IntervalIntegrable (fun u => ψ (s * u)) volume 1 2 := fun s hs =>
    (hψ_mono.comp fun _ _ h => mul_le_mul_of_nonneg_left h hs).intervalIntegrable
  have hg_zero : g 0 = 0 := by simp [g, ψ, hφ_zero]
  -- `g` is nondecreasing, because `ψ` is.
  have hg_mono : MonotoneOn g (Ici 0) := fun s hs s' hs' hss' =>
    intervalIntegral.integral_mono_on (by norm_num) (hg_int s hs) (hg_int s' hs') fun u hu =>
      hψ_mono (mul_le_mul_of_nonneg_right hss' (by linarith [hu.1]))
  -- `φ s ≤ g s ≤ φ (2s)`: for `u ∈ [1, 2]`, `ψ s ≤ ψ (s u) ≤ ψ (2s)`, and the window has
  -- length `1`.
  have hg_ge : ∀ s ≥ 0, φ s ≤ g s := fun s hs => by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
      intervalIntegral.intervalIntegrable_const (hg_int s hs) fun u hu =>
        hψ_mono (le_mul_of_one_le_right hs hu.1)
    norm_num [hψ_eq s hs] at h
    exact h
  have hg_le : ∀ s ≥ 0, g s ≤ φ (2 * s) := fun s hs => by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2)
      (hg_int s hs) intervalIntegral.intervalIntegrable_const fun u hu =>
        hψ_mono (by nlinarith [hu.2] : s * u ≤ 2 * s)
    norm_num [hψ_eq (2 * s) (by linarith)] at h
    exact h
  have hg_nonneg : ∀ s ≥ 0, 0 ≤ g s := fun s hs =>
    (hψ_eq s hs ▸ hψ_nonneg s).trans (hg_ge s hs)
  -- Step 3. `g` is continuous on `[0, ∞)`.
  -- At `0`: `g` is squeezed between `0` and `φ (2s)`, which tends to `φ 0 = 0`.
  have hg_cont_zero : ContinuousWithinAt g (Ici 0) 0 := by
    have h_upper : Tendsto (fun s => φ (2 * s)) (𝓝[≥] 0) (𝓝 0) := by
      have h := hφ_cont.comp_of_eq (continuousWithinAt_id.const_mul 2)
        (fun s (hs : 0 ≤ s) => by simp only [mem_Ici, id]; linarith) (mul_zero 2)
      simpa [hφ_zero] using h.tendsto
    rw [ContinuousWithinAt, hg_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
      (eventually_nhdsWithin_of_forall hg_nonneg) (eventually_nhdsWithin_of_forall hg_le)
  -- At `s > 0`: substituting `x = s u` gives `g s = s⁻¹ (Φ (2s) - Φ s)`, where `Φ` is the
  -- (continuous) primitive of `ψ`.
  set Φ : ℝ → ℝ := fun b => ∫ x in (0 : ℝ)..b, ψ x
  have hΦ_cont : Continuous Φ := intervalIntegral.continuous_primitive hψ_int 0
  have hg_eq : ∀ s ≠ 0, g s = s⁻¹ * (Φ (s * 2) - Φ (s * 1)) := fun s hs => by
    simp only [g, Φ]
    rw [intervalIntegral.integral_comp_mul_left _ hs, smul_eq_mul,
      intervalIntegral.integral_interval_sub_left (hψ_int _ _) (hψ_int _ _)]
  have hg_cont_pos : ∀ s > 0, ContinuousAt g s := fun s hs => by
    have h : ContinuousAt (fun t => t⁻¹ * (Φ (t * 2) - Φ (t * 1))) s :=
      (continuousAt_inv₀ hs.ne').mul (by fun_prop)
    exact h.congr ((eventually_ne_nhds hs.ne').mono fun t ht => (hg_eq t ht).symm)
  have hg_cont : ContinuousOn g (Ici 0) := by
    intro s hs
    rcases (mem_Ici.mp hs).eq_or_lt with rfl | hs_pos
    · exact hg_cont_zero
    · exact (hg_cont_pos s hs_pos).continuousWithinAt
  -- Step 4. `f s = s + g s` has every required property.
  refine ⟨fun s => s + g s, ?_, ?_, ?_, ?_, ?_⟩
  · -- `f 0 = 0`
    simp [hg_zero]
  · -- continuous
    exact continuousOn_id.add hg_cont
  · -- strictly increasing: `s` is strictly increasing and `g` is nondecreasing
    intro s hs s' hs' hss'
    exact add_lt_add_of_lt_of_le hss' (hg_mono hs hs' hss'.le)
  · -- unbounded: `f s ≥ s`
    refine tendsto_atTop_mono' _ ((eventually_ge_atTop 0).mono fun s hs => ?_) tendsto_id
    simpa using hg_nonneg s hs
  · -- majorizes `φ`: `φ s ≤ g s ≤ s + g s`
    intro s hs
    linarith [hg_ge s hs]

/-- A monotonically non-decreasing function on `[0, r]`, continuous at `0` with value `0`, can be
    upper-bounded by a strictly monotonic continuous function.

Proved by clamping `φ` beyond `r` and invoking the global version. -/
@[blueprint "lem:exists-strictMono-upper-bound"
  (title := "Class $\\mathcal{K}$ majorant on a bounded interval")
  (latexEnv := "lemma")
  (statement := /-- Let $r > 0$ and let $\varphi$ satisfy $\varphi(0) = 0$, be monotone on
    $[0, r]$, and be continuous at $0$ from the right.  Then there are $b > 0$ and an $f$ with
    $f(0) = 0$, $f(r) = b$, $f$ continuous and strictly increasing on $[0, r]$, and
    $\varphi(s) \le f(s)$ for all $s \in [0, r]$. -/)
  (proof := /-- Clamp $\varphi$ to $\varphi_{\mathrm{ext}}(s) = \varphi(\min(s, r))$, which
    is monotone on all of $[0,\infty)$, still vanishes at $0$ and agrees with $\varphi$ near
    $0$ (so is still continuous there), and apply
    \cref{lem:exists-strictMono-upper-bound-global}.  Restricting the resulting majorant to
    $[0, r]$ gives $f$; $b = f(r) > 0$ because $f$ is strictly increasing from $f(0) = 0$. -/)]
lemma exists_strictMono_upper_bound (r : ℝ) (hr : 0 < r) (φ : ℝ → ℝ)
    (hφ_zero : φ 0 = 0)
    (hφ_mono : MonotoneOn φ (Set.Icc 0 r))
    (hφ_cont : ContinuousWithinAt φ (Set.Icc 0 r) 0) :
    ∃ (f : ℝ → ℝ) (b : ℝ), 0 < b ∧
      f 0 = 0 ∧ f r = b ∧
      ContinuousOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc 0 r) ∧
      ∀ s, 0 ≤ s → s ≤ r → φ s ≤ f s := by
  -- Extend φ to [0, ∞) by clamping: φ_ext s = φ s for s ≤ r, φ r for s > r
  let φ_ext : ℝ → ℝ := fun s => if s ≤ r then φ s else φ r
  have hφ_ext_zero : φ_ext 0 = 0 := by simp [φ_ext, hr.le, hφ_zero]
  have hφ_ext_mono : MonotoneOn φ_ext (Set.Ici 0) := by
    intro s₁ hs₁ s₂ _ h_le
    simp only [φ_ext]
    split_ifs with h1 h2
    · exact hφ_mono ⟨hs₁, h_le.trans h2⟩ ⟨hs₁.trans h_le, h2⟩ h_le   -- both ≤ r
    · exact hφ_mono ⟨hs₁, h1⟩ ⟨hr.le, le_rfl⟩ h1                     -- s₁ ≤ r < s₂
    · linarith [not_le.mp h1]                -- s₁ > r, s₂ ≤ r: impossible
    · exact le_refl _                        -- both > r
  -- φ_ext agrees with φ on [0, r], which is a neighbourhood of 0 within [0, ∞)
  have hφ_ext_cont : ContinuousWithinAt φ_ext (Set.Ici 0) 0 :=
    (hφ_cont.congr (fun s hs => if_pos hs.2) (if_pos hr.le)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE hr)
  -- Apply the global version to φ_ext
  obtain ⟨f, hf_zero, hf_cont, hf_mono, _, hf_bound⟩ :=
    exists_strictMono_upper_bound_global φ_ext hφ_ext_zero hφ_ext_mono hφ_ext_cont
  refine ⟨f, f r, ?_, hf_zero, rfl,
    hf_cont.mono Set.Icc_subset_Ici_self,
    hf_mono.mono Set.Icc_subset_Ici_self,
    fun s hs₁ hs₂ => ?_⟩
  · -- f r > 0: f strictly mono, f 0 = 0, r > 0
    have h := hf_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr.le) hr
    linarith [hf_zero ▸ h]
  · -- φ s ≤ φ_ext s ≤ f s for s ≤ r
    have h := hf_bound s hs₁
    simp only [φ_ext, if_pos hs₂] at h
    exact h

/-! ## Joint continuity of separately monotone functions -/

/-- A function of two real variables that is monotone in the first, antitone in the second, and
continuous in each variable separately is jointly continuous.

Near `(r₀, s₀)` the monotonicity sandwiches `f r s` between the corner values
`f r₋ s₊ ≤ f r s ≤ f r₊ s₋`, and separate continuity lets both corners be chosen close to
`f r₀ s₀`: first move the second coordinate, then the first. -/
@[blueprint "lem:continuous-uncurry-of-monotone-antitone"
  (title := "Joint continuity from separate continuity and monotonicity")
  (latexEnv := "lemma")
  (statement := /-- Let $f : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ be nondecreasing in
    its first argument, nonincreasing in its second, and continuous in each argument
    separately.  Then $f$ is jointly continuous. -/)
  (proof := /-- Near $(r_0, s_0)$, monotonicity gives $f(r_-, s_+) \le f(r, s) \le f(r_+, s_-)$
    whenever $r_- < r < r_+$ and $s_- < s < s_+$.  Given $u > f(r_0, s_0)$, continuity of
    $f(r_0, \cdot)$ gives $s_- < s_0$ with $f(r_0, s_-) < u$, and then continuity of
    $f(\cdot, s_-)$ gives $r_+ > r_0$ with $f(r_+, s_-) < u$; so $f < u$ on the neighbourhood
    $(-\infty, r_+) \times (s_-, \infty)$.  The lower bound is symmetric. -/)]
theorem continuous_uncurry_of_monotone_antitone {f : ℝ → ℝ → ℝ}
    (hf_mono : ∀ s, Monotone (f · s)) (hf_anti : ∀ r, Antitone (f r))
    (hf_cont_fst : ∀ s, Continuous (f · s)) (hf_cont_snd : ∀ r, Continuous (f r)) :
    Continuous (Function.uncurry f) := by
  refine continuous_iff_continuousAt.mpr fun ⟨r₀, s₀⟩ => tendsto_order.mpr ⟨?_, ?_⟩
  · -- lower bound: pick `s₁ > s₀`, then `r₁ < r₀`, with `f r₁ s₁ > l`
    intro l hl
    obtain ⟨s₁, hs₁, h₁⟩ := ((hf_cont_snd r₀).continuousAt.eventually (lt_mem_nhds hl)).exists_gt
    obtain ⟨r₁, hr₁, h₂⟩ := ((hf_cont_fst s₁).continuousAt.eventually (lt_mem_nhds h₁)).exists_lt
    filter_upwards [prod_mem_nhds (Ioi_mem_nhds hr₁) (Iio_mem_nhds hs₁)] with ⟨r, s⟩ ⟨hr, hs⟩
    exact h₂.trans_le ((hf_mono s₁ (le_of_lt hr)).trans (hf_anti r (le_of_lt hs)))
  · -- upper bound: pick `s₁ < s₀`, then `r₁ > r₀`, with `f r₁ s₁ < u`
    intro u hu
    obtain ⟨s₁, hs₁, h₁⟩ := ((hf_cont_snd r₀).continuousAt.eventually (gt_mem_nhds hu)).exists_lt
    obtain ⟨r₁, hr₁, h₂⟩ := ((hf_cont_fst s₁).continuousAt.eventually (gt_mem_nhds h₁)).exists_gt
    filter_upwards [prod_mem_nhds (Iio_mem_nhds hr₁) (Ioi_mem_nhds hs₁)] with ⟨r, s⟩ ⟨hr, hs⟩
    exact ((hf_anti r (le_of_lt hs)).trans (hf_mono s₁ (le_of_lt hr))).trans_lt h₂
