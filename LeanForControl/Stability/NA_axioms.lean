import Mathlib.Analysis.Calculus.FDeriv.Basic
import LeanForControl.Stability.DefsNonAutonomous

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

import Architect

open MeasureTheory intervalIntegral Set Filter Topology


variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)


private noncomputable def validTSet (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : Set ℝ :=
  {T | 0 ≤ T ∧ ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < r → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η}


private noncomputable def Tbar_fn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : ℝ :=
  sInf (validTSet f x_eq η r)



open Set Filter Topology MeasureTheory intervalIntegral

/-- For any locally integrable `f`, the sliding half-window integral
    `η ↦ ∫ s in (η/2)..η, f s` is continuous on `(0, ∞)`. -/
@[blueprint "lem:continuousOnHalfWindowIntegral"
  (statement := /-- If $f$ is locally integrable on $(0,\infty)$, the map
    $\eta \mapsto \int_{\eta/2}^{\eta} f(s)\,ds$ is continuous on $(0,\infty)$. -/)]
lemma continuousOn_halfWindow_integral {f : ℝ → ℝ}
    (hf_int : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b) :
    ContinuousOn (fun η => ∫ s in (η / 2)..η, f s) (Set.Ioi 0) := by
  intro η₀ hη₀
  -- We are on an open domain, so prove the stronger ContinuousAt
  apply ContinuousAt.continuousWithinAt
  have hη₀_pos : 0 < η₀ := hη₀
  -- Fixed window [A, B] = [η₀/4, 2η₀] around η₀ for the primitive bounds
  let A := η₀ / 4
  let B := 2 * η₀
  have hA_pos : 0 < A := by positivity
  have hB_pos : 0 < B := by positivity
  have hAB : A ≤ B := by change η₀ / 4 ≤ 2 * η₀; linarith
  have h_prim : ContinuousOn (fun x => ∫ s in A..x, f s) (Set.Icc A B) := by
    have h := continuousOn_primitive_interval' (hf_int A B hA_pos hB_pos)
      (left_mem_uIcc (b := B))
    rwa [uIcc_of_le hAB] at h
  have hη₀_in : η₀ ∈ Set.Ioo A B :=
    ⟨by change η₀ / 4 < η₀; linarith, by change η₀ < 2 * η₀; linarith⟩
  have h_half_in : η₀ / 2 ∈ Set.Ioo A B :=
    ⟨by change η₀ / 4 < η₀ / 2; linarith, by change η₀ / 2 < 2 * η₀; linarith⟩
  have h_cont1 : ContinuousAt (fun η => ∫ s in A..η, f s) η₀ :=
    h_prim.continuousAt (Icc_mem_nhds hη₀_in.1 hη₀_in.2)
  have h_cont2 : ContinuousAt (fun η => ∫ s in A..(η / 2), f s) η₀ :=
    (h_prim.continuousAt (Icc_mem_nhds h_half_in.1 h_half_in.2)).comp
      (f := fun η : ℝ => η / 2) (continuous_id.div_const 2).continuousAt
  -- Locally around η₀, integral splits as (∫ A..η) - (∫ A..η/2) = ∫ η/2..η
  have h_eq : ∀ᶠ η in 𝓝 η₀, (∫ s in A..η, f s) - (∫ s in A..(η / 2), f s)
    = ∫ s in (η / 2)..η, f s := by
    filter_upwards [Ioo_mem_nhds hη₀_in.1 hη₀_in.2] with η hη
    have hη_pos : 0 < η := hA_pos.trans hη.1
    have hadd := integral_add_adjacent_intervals
      (hf_int A (η / 2) hA_pos (by linarith))
      (hf_int (η / 2) η (by linarith) hη_pos)
    linarith
  exact (h_cont1.sub h_cont2).congr h_eq


/-- The scaled half-window average `η ↦ (2/η) * ∫ s in (η/2)..η, f s` is antitone on `(0, ∞)`
    whenever `f` is antitone on `(0, ∞)`. -/
@[blueprint "lem:antitoneOnHalfWindowAverage"
  (statement := /-- If $f$ is antitone on $(0,\infty)$, the map
    $\eta \mapsto \tfrac{2}{\eta}\int_{\eta/2}^{\eta} f(s)\,ds$ is antitone on $(0,\infty)$. -/)]
lemma antitoneOn_halfWindow_average {f : ℝ → ℝ}
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b) :
    AntitoneOn (fun η => (2 / η) * ∫ s in (η / 2)..η, f s) (Set.Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ h_le
  have hη₁_pos : (0 : ℝ) < η₁ := hη₁
  have hη₂_pos : (0 : ℝ) < η₂ := hη₂
  -- Rewrite: (2/η) * ∫ (η/2)..η, f = 2 * ∫ (1/2)..1, f(η·) via substitution s = η*t
  have hrw : ∀ η : ℝ, 0 < η → (2 / η) * ∫ s in (η / 2)..η, f s =
      2 * ∫ t in (1/2 : ℝ)..(1 : ℝ), f (η * t) := fun η hη => by
    have key : η • ∫ x in (1/2 : ℝ)..(1 : ℝ), f (η * x) =
        ∫ x in η * (1/2 : ℝ)..η * (1 : ℝ), f x := smul_integral_comp_mul_left f η
    simp only [smul_eq_mul, mul_one, show η * (1 / 2 : ℝ) = η / 2 from by ring] at key
    rw [← key, ← mul_assoc, div_mul_cancel₀ 2 hη.ne']
  dsimp only
  rw [hrw η₁ hη₁_pos, hrw η₂ hη₂_pos]
  -- Need: 2 * ∫ (1/2)..1, f(η₂·) ≤ 2 * ∫ (1/2)..1, f(η₁·)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  -- Integrability of f(ηᵢ·) on [1/2, 1]
  have mk_int : ∀ η : ℝ, 0 < η →
      IntervalIntegrable (fun t => f (η * t)) volume (1/2 : ℝ) 1 := fun η hη => by
    have h := (hf_int (η / 2) η (by linarith) hη).comp_mul_left (c := η)
    have heq1 : η / 2 / η = 1 / 2 := by field_simp
    rwa [heq1, div_self hη.ne'] at h
  -- Pointwise: f(η₂·t) ≤ f(η₁·t) for t ∈ [1/2, 1] since η₁·t ≤ η₂·t and f antitone
  refine integral_mono_on (by norm_num) (mk_int η₂ hη₂_pos) (mk_int η₁ hη₁_pos)
    fun t ht => hf_anti (mul_pos hη₁_pos (by linarith [ht.1]))
      (mul_pos hη₂_pos (by linarith [ht.1]))
      (mul_le_mul_of_nonneg_right h_le (by linarith [ht.1]))


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


/-- If `f` is nonneg, antitone on `(0, ∞)`, locally integrable, and tends to `0` at `+∞`,
    then the scaled half-window average `η ↦ (2/η) * ∫ s in (η/2)..η, f s` also tends to `0`
    at `+∞`. -/
@[blueprint "lem:tendstoHalfWindowAverageZero"
  (statement := /-- Let $f : \mathbb{R} \to \mathbb{R}$ be nonneg, antitone on $(0,\infty)$,
    locally integrable, and satisfy $f(s) \to 0$ as $s \to +\infty$.  Then
    $\tfrac{2}{\eta}\int_{\eta/2}^{\eta} f(s)\,ds \to 0$ as $\eta \to +\infty$. -/)]
lemma tendsto_halfWindow_average_zero {f : ℝ → ℝ}
    (hf_nonneg : ∀ s > 0, 0 ≤ f s)
    (hf_anti : AntitoneOn f (Set.Ioi 0))
    (hf_int : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b)
    (hf_tendsto : Filter.Tendsto f Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun η => (2 / η) * ∫ s in (η / 2)..η, f s) Filter.atTop (nhds 0) := by
  -- Squeeze the average between 0 and f(η / 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => 0) (h := fun η => f (η / 2))
  · -- Subgoal 1: Limit of the lower bound (0) is 0
    exact tendsto_const_nhds
  · -- Subgoal 2: Limit of the upper bound f(η / 2) is 0
    have h_half_atTop : Filter.Tendsto (fun η : ℝ => η / 2) Filter.atTop Filter.atTop :=
      tendsto_id.atTop_div_const zero_lt_two
    exact hf_tendsto.comp h_half_atTop
  · -- Subgoal 3: Lower bound (0 ≤ Average)
    filter_upwards [Filter.Ioi_mem_atTop 0] with η hη
    have h_half_pos : 0 < η / 2 := half_pos hη
    refine mul_nonneg (div_nonneg zero_le_two hη.le)
      (integral_nonneg (half_le_self hη.le) fun s hs => ?_)
    exact hf_nonneg s (h_half_pos.trans_le hs.1)
  · -- Subgoal 4: Upper bound (Average ≤ f(η / 2))
    filter_upwards [Filter.Ioi_mem_atTop 0] with η hη
    have hη_pos : 0 < η := hη
    have h_half_pos : 0 < η / 2 := half_pos hη_pos
    have h_le : η / 2 ≤ η := half_le_self hη_pos.le
    -- Bound the integral by replacing f(s) with its maximum value f(η/2)
    have h_int_le : ∫ s in (η / 2)..η, f s ≤ ∫ s in (η / 2)..η, f (η / 2) := by
      refine integral_mono_on h_le (hf_int (η / 2) η h_half_pos hη_pos)
        intervalIntegrable_const fun s hs => ?_
      exact hf_anti h_half_pos (h_half_pos.trans_le hs.1) hs.1
    -- Evaluate the integral of the constant and rescale
    have h_const_int : ∫ s in (η / 2)..η, f (η / 2) = (η / 2) * f (η / 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [h_const_int] at h_int_le
    have h_mul_le := mul_le_mul_of_nonneg_left h_int_le (div_nonneg zero_le_two hη_pos.le)
    have h_rhs : (2 / η) * ((η / 2) * f (η / 2)) = f (η / 2) := by
      field_simp
    rwa [h_rhs] at h_mul_le
