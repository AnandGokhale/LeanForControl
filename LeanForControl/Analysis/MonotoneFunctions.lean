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




lemma tendsto_min_sqrt_mul_zero {c : ℝ} (hc : 0 ≤ c)
    {U : ℝ → ℝ} (hU : Filter.Tendsto U Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun s => min c (Real.sqrt (c * U s))) Filter.atTop (nhds 0) := by
  refine squeeze_zero
    (fun s => le_min hc (Real.sqrt_nonneg _))
    (fun s => min_le_right _ _)
    ?_
  have h_mul : Filter.Tendsto (fun s => c * U s) Filter.atTop (nhds 0) := by
    simpa using Filter.Tendsto.const_mul c hU
  simpa [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h_mul
