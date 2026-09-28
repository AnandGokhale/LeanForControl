import LeanForControl.Stability.DefsNonAutonomous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue


import Architect

open MeasureTheory intervalIntegral Set Filter Topology

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Antitone function inverses -/

/-- A continuous function `W : ℝ → ℝ` on `(0, ∞)` that tends to `+∞` near `0⁺` and to `0`
    at `+∞` surjects onto `(0, ∞)`: every `s > 0` lies in the image `W '' (Ioi 0)`. -/
@[blueprint "lem:memImageIoiOfTendsto"
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
