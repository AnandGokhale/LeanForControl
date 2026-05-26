import LeanForControl.Stability.DefsNonAutonomous
import LeanForControl.Stability.classK
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue
import Architect

open MeasureTheory intervalIntegral Set Filter Topology

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Moving window integrals -/

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
  set A := η₀ / 4
  have hA_pos : 0 < A := by positivity
  have h_prim : ContinuousOn (fun x => ∫ s in A..x, f s) (Set.Icc A (2 * η₀)) := by
    have h := continuousOn_primitive_interval' (hf_int A (2 * η₀) hA_pos (by linarith))
      (left_mem_uIcc (b := (2 * η₀)))
    rwa [uIcc_of_le (by change η₀ / 4 ≤ 2 * η₀; linarith)] at h
  have hη₀_in : η₀ ∈ Set.Ioo A (2 * η₀) := ⟨by simp only [A]; linarith, by linarith⟩
  have hh_in  : η₀ / 2 ∈ Set.Ioo A (2 * η₀) := ⟨by simp only [A]; linarith, by linarith⟩
  have cont1 : ContinuousAt (fun η => ∫ s in A..η, f s) η₀ :=
    h_prim.continuousAt (Icc_mem_nhds hη₀_in.1 hη₀_in.2)
  have cont2 : ContinuousAt (fun η => ∫ s in A..(η / 2), f s) η₀ :=
    (h_prim.continuousAt (Icc_mem_nhds hh_in.1 hh_in.2)).comp
      (f := fun η : ℝ => η / 2) (continuous_id.div_const 2).continuousAt
  refine (cont1.sub cont2).congr ?_
  filter_upwards [Ioo_mem_nhds hη₀_in.1 hη₀_in.2] with η hη
  have hη_pos : 0 < η := hA_pos.trans hη.1
  linarith [integral_add_adjacent_intervals
    (hf_int A (η / 2) hA_pos (by linarith))
    (hf_int (η / 2) η (by linarith) hη_pos)]

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
  gcongr
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
      (by gcongr; linarith [ht.1])


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
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ => 0) (h := fun η => f (η / 2))
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
    have h_half_pos : 0 < η / 2 := half_pos hη
    have h_le : η / 2 ≤ η := half_le_self hη.le
    -- Bound the integral by replacing f(s) with its maximum value f(η/2)
    have h_int_le : ∫ s in (η / 2)..η, f s ≤ ∫ s in (η / 2)..η, f (η / 2) := by
      refine integral_mono_on h_le (hf_int (η / 2) η h_half_pos hη)
        intervalIntegral.intervalIntegrable_const fun s hs => ?_
      exact hf_anti h_half_pos (h_half_pos.trans_le hs.1) hs.1
    have hη_pos : 0 < η := Set.mem_Ioi.mp hη
    calc (2 / η) * ∫ s in (η / 2)..η, f s
        ≤ (2 / η) * ∫ s in (η / 2)..η, f (η / 2) := by gcongr
      _ = (2 / η) * ((η / 2) * f (η / 2)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring_nf
      _ = f (η / 2) := by field_simp [hη_pos.ne']

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

/-! ## T̄ — optimal uniform convergence time -/

private noncomputable def validTSet (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : Set ℝ :=
  {T | 0 ≤ T ∧ ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < r → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η}

/-- `Tbar_fn f x_eq η r` is the infimum of valid convergence times from the `r`-ball to the
    `η`-ball: the smallest `T` that works for all trajectories simultaneously. -/
noncomputable def Tbar_fn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) : ℝ :=
  sInf (validTSet f x_eq η r)

private lemma validTSet_bddBelow (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (η r : ℝ) :
    BddBelow (validTSet f x_eq η r) :=
  ⟨0, fun _ hT => hT.1⟩

private lemma validTSet_nonempty (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    (validTSet f x_eq η r).Nonempty := by
  obtain ⟨T, hT_pos, hT_prop⟩ := hconv η hη
  exact ⟨T, hT_pos.le, fun t₀ ht₀ φ hφ h_init t ht =>
    hT_prop t₀ ht₀ φ hφ (h_init.trans_le hr.2) t ht⟩

private lemma Tbar_nonneg_of (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {η : ℝ} (hη : 0 < η) {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    0 ≤ Tbar_fn f x_eq η r :=
  le_csInf (validTSet_nonempty f x_eq hconv hη hr) (fun _ hT => hT.1)

private lemma Tbar_antitone (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    AntitoneOn (fun η => Tbar_fn f x_eq η r) (Set.Ioi 0) := by
  intro η₁ hη₁ η₂ hη₂ h_le
  exact csInf_le_csInf (validTSet_bddBelow f x_eq η₂ r)
    (validTSet_nonempty f x_eq hconv hη₁ hr)
    fun T ⟨hT_nn, hT_prop⟩ => ⟨hT_nn,
      fun t₀ ht₀ φ hφ h_init t ht => (hT_prop t₀ ht₀ φ hφ h_init t ht).trans_le h_le⟩

private lemma Tbar_intervalIntegrable (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) :
    IntervalIntegrable (fun s => Tbar_fn f x_eq s r) MeasureTheory.volume a b := by
  apply AntitoneOn.intervalIntegrable
  exact (Tbar_antitone f x_eq hconv hr).mono fun s hs => by
    rw [Set.uIcc_of_le hab] at hs; exact Set.mem_Ioi.mpr (ha.trans_le hs.1)

private lemma Tbar_intervalIntegrable_of_pos (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun s => Tbar_fn f x_eq s r) MeasureTheory.volume a b := by
  rcases le_total a b with hab | hab
  · exact Tbar_intervalIntegrable f x_eq hconv hr hab ha
  · exact (Tbar_intervalIntegrable f x_eq hconv hr hab hb).symm

private lemma Tbar_zero_of_classK_bound (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < a_α → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {a : ℝ} (ha_lt_aα : a < a_α) (ha_le_c : a ≤ c)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) {η : ℝ} (h_le : α.toFun r ≤ η) :
    Tbar_fn f x_eq η r = 0 := by
  have hr_lt_aα : r < a_α := hr.2.trans_lt ha_lt_aα
  have hr_Ico : r ∈ Set.Ico 0 a_α := ⟨hr.1.le, hr_lt_aα⟩
  have h_alpha_pos : 0 < α.toFun r :=
    α.map_zero ▸ α.strict_mono ⟨le_refl 0, α.ha⟩ hr_Ico hr.1
  have hη_pos : 0 < η := h_alpha_pos.trans_le h_le
  refine le_antisymm (csInf_le (validTSet_bddBelow f x_eq η r) ⟨le_refl 0, ?_⟩)
    (le_csInf (validTSet_nonempty f x_eq hconv hη_pos ⟨hr.1, hr.2.trans ha_le_c⟩)
      (fun _ hT => hT.1))
  intro t₀ ht₀ φ hφ h_init t ht
  have h_stab := hα_bound t₀ ht₀ φ hφ (h_init.trans hr_lt_aα) t (by linarith)
  have h_strict := α.strict_mono ⟨norm_nonneg _, h_init.trans hr_lt_aα⟩ hr_Ico h_init
  exact (h_stab.trans_lt h_strict).trans_le h_le


private lemma Tbar_mono_r (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Set.Ioc 0 c) (hr₂ : r₂ ∈ Set.Ioc 0 c) (h_le : r₁ ≤ r₂)
    {η : ℝ} (hη : 0 < η) :
    Tbar_fn f x_eq η r₁ ≤ Tbar_fn f x_eq η r₂ := by
  exact csInf_le_csInf (validTSet_bddBelow f x_eq η r₁)
    (validTSet_nonempty f x_eq hconv hη hr₂)
    fun T hT => ⟨hT.1, fun t₀ ht₀ φ hφ h_init t ht =>
      hT.2 t₀ ht₀ φ hφ (h_init.trans_le h_le) t ht⟩

/-! ## W — sliding average of T̄ -/

/-- `W_fn f x_eq r η = (2/η) ∫_{η/2}^{η} [T̄(s,r) + r/η] ds`
    (Sontag 1998). Strictly decreasing in `η`, strictly increasing in `r`. -/
noncomputable def W_fn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (r η : ℝ) : ℝ :=
  (2 / η) * ∫ s in (η / 2)..η, (Tbar_fn f x_eq s r + r / η)

private lemma W_pos (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    0 < W_fn f x_eq r η := by
  have h_int_Tbar := Tbar_intervalIntegrable f x_eq hconv hr (by linarith : η / 2 ≤ η) (half_pos hη)
  have h_int_sum : IntervalIntegrable (fun s => Tbar_fn f x_eq s r + r / η) volume (η / 2) η :=
    h_int_Tbar.add intervalIntegral.intervalIntegrable_const
  have h_bound : ∫ s in (η / 2)..η, r / η ≤ ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
    refine intervalIntegral.integral_mono_on (by linarith)
      intervalIntegral.intervalIntegrable_const h_int_sum (fun s hs => ?_)
    linarith [Tbar_nonneg_of f x_eq hconv (by linarith [hs.1] : 0 < s) hr]
  have h_const_int : ∫ s in (η / 2)..η, r / η = r / 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp [hη.ne']; ring
  calc (0 : ℝ) < r / η := div_pos hr.1 hη
    _ = (2 / η) * (r / 2) := by ring
    _ ≤ (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
        gcongr; linarith [h_bound, h_const_int]

private lemma W_ge_Tbar (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    Tbar_fn f x_eq η r + r / η ≤ W_fn f x_eq r η := by
  have h_int_Tbar := Tbar_intervalIntegrable f x_eq hconv hr (by linarith : η / 2 ≤ η) (half_pos hη)
  have h_int_sum : IntervalIntegrable (fun s => Tbar_fn f x_eq s r + r / η) volume (η / 2) η :=
    h_int_Tbar.add intervalIntegral.intervalIntegrable_const
  have h_anti := Tbar_antitone f x_eq hconv hr
  have h_integral_bound :
      ∫ s in (η / 2)..η, Tbar_fn f x_eq η r + r / η ≤
      ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegral.intervalIntegrable_const h_int_sum
      (fun s hs => ?_)
    have hs_pos : 0 < s := by linarith [hs.1]
    linarith [h_anti (Set.mem_Ioi.mpr hs_pos) (Set.mem_Ioi.mpr hη) hs.2]
  have h_const_int :
      ∫ s in (η / 2)..η, Tbar_fn f x_eq η r + r / η =
      (η / 2) * (Tbar_fn f x_eq η r + r / η) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  dsimp [W_fn]
  calc Tbar_fn f x_eq η r + r / η
      = (2 / η) * ((η / 2) * (Tbar_fn f x_eq η r + r / η)) := by
        rw [← mul_assoc, show (2 / η) * (η / 2) = 1 from by field_simp, one_mul]
    _ ≤ (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r + r / η := by
        rw [← h_const_int]; gcongr

/-- Unpacking the infimum: If s > Tbar(η, r), then the trajectory has already reached the η-ball. -/
private lemma norm_le_of_Tbar_lt {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {η r s t₀ t : ℝ} {φ : ℝ → ℝⁿ}
  (hne : (validTSet f x_eq η r).Nonempty)
  (hlt : Tbar_fn f x_eq η r < s) (ht₀ : 0 ≤ t₀)
  (hφ : IsTrajectoryNA φ f) (h_init : ‖φ t₀ - x_eq‖ < r)
  (ht : t₀ + s ≤ t) :
  ‖φ t - x_eq‖ ≤ η := by
  -- sInf(validTSet) < s and validTSet nonempty ⇒ ∃ T ∈ validTSet, T < s ⇒ t₀ + T ≤ t
  obtain ⟨T, ⟨_, hT_prop⟩, hT_lt⟩ := exists_lt_of_csInf_lt hne hlt
  exact (hT_prop t₀ ht₀ φ hφ h_init t (by linarith)).le

private lemma W_fn_eq (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) {η : ℝ} (hη : 0 < η) :
    W_fn f x_eq r η = (2 / η) * (∫ s in (η / 2)..η, Tbar_fn f x_eq s r) + r / η := by
  have hη_ne : η ≠ 0 := ne_of_gt hη
  simp only [W_fn]
  rw [intervalIntegral.integral_add
    (Tbar_intervalIntegrable f x_eq hconv hr (le_of_lt (half_lt_self hη)) (half_pos hη))
    intervalIntegral.intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  have h_const : (η - η / 2) * (r / η) = r / 2 := by field_simp; ring
  rw [h_const]; field_simp [hη_ne]

lemma W_fn_continuousOn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) : ContinuousOn (W_fn f x_eq r) (Set.Ioi 0) := by
  have h_int_cont : ContinuousOn (fun η => ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
    (Set.Ioi 0) := continuousOn_halfWindow_integral (Tbar_intervalIntegrable_of_pos f x_eq hconv hr)
  have h_rhs_cont : ContinuousOn
      (fun η => (2 / η) * (∫ s in (η / 2)..η, Tbar_fn f x_eq s r) + r / η) (Set.Ioi 0) := by
    refine ContinuousOn.add (ContinuousOn.mul ?_ h_int_cont) ?_ <;>
      exact fun η hη =>
        (continuousAt_const.div continuousAt_id (Set.mem_Ioi.mp hη).ne').continuousWithinAt
  exact h_rhs_cont.congr (fun η hη => W_fn_eq f x_eq hconv hr hη)

lemma W_fn_strictAntiOn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) : StrictAntiOn (W_fn f x_eq r) (Set.Ioi 0) := by
  have h_avg_anti : AntitoneOn (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
      (Set.Ioi 0) :=
    antitoneOn_halfWindow_average (Tbar_antitone f x_eq hconv hr)
      (Tbar_intervalIntegrable_of_pos f x_eq hconv hr)
  have h_r_div_strict : StrictAntiOn (fun η => r / η) (Set.Ioi 0) := fun η₁ hη₁ η₂ hη₂ h_lt =>
    (div_lt_div_iff₀ hη₂ hη₁).mpr (mul_lt_mul_of_pos_left h_lt hr.1)
  intro η₁ hη₁ η₂ hη₂ h_lt
  rw [W_fn_eq f x_eq hconv hr hη₁, W_fn_eq f x_eq hconv hr hη₂]
  linarith [h_avg_anti hη₁ hη₂ h_lt.le, h_r_div_strict hη₁ hη₂ h_lt]

lemma W_fn_tendsto_nhdsGT (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 c) :
    Filter.Tendsto (W_fn f x_eq r) (𝓝[>] 0) Filter.atTop := by
  have h_r_pos : 0 < r := hr.1
  -- W(η) is bounded below by r / η
  have h_lower_bound : ∀ᶠ η in 𝓝[>] (0 : ℝ), r / η ≤ W_fn f x_eq r η := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    have h_ge := W_ge_Tbar f x_eq hconv hr hη
    linarith [Tbar_nonneg_of f x_eq hconv hη ⟨hr.1, hr.2⟩]
  -- The limit of r * (1/η) as η → 0⁺ is ∞; squeeze theorem pushes W(η) to ∞
  have h_r_div : Filter.Tendsto (fun η : ℝ => r / η) (𝓝[>] 0) Filter.atTop := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul_atTop h_r_pos tendsto_inv_nhdsGT_zero
  exact tendsto_atTop_mono' (𝓝[>] 0) h_lower_bound h_r_div

lemma W_fn_tendsto_atTop (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < a_α → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {a : ℝ} (_ha : 0 < a) (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a) :
    Filter.Tendsto (W_fn f x_eq r) Filter.atTop (nhds 0) := by
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  have h_avg : Filter.Tendsto (fun η => (2 / η) * ∫ s in (η / 2)..η, Tbar_fn f x_eq s r)
    Filter.atTop (nhds 0) := by
    apply tendsto_halfWindow_average_zero
    · exact fun s hs => Tbar_nonneg_of f x_eq hconv hs hr_c
    · exact Tbar_antitone f x_eq hconv hr_c
    · exact Tbar_intervalIntegrable_of_pos f x_eq hconv hr_c
    · -- For large enough η, every trajectory starting within r is already within η
      -- (the class K bound α(r) is a finite ceiling), so Tbar = 0 eventually.
      have h_eventually_zero : ∀ᶠ η in Filter.atTop, Tbar_fn f x_eq η r = 0 := by
        filter_upwards [Filter.eventually_ge_atTop (α.toFun r)] with η hη
        exact Tbar_zero_of_classK_bound f x_eq hconv α hα_bound ha_lt_aα ha_le_c hr hη
      exact tendsto_const_nhds.congr' (h_eventually_zero.mono (fun _ h => h.symm))
  have h_rdiv : Filter.Tendsto (fun η => r / η) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.const_mul r tendsto_inv_atTop_zero
  have h_sum := h_avg.add h_rdiv
  simp only [add_zero] at h_sum
  refine h_sum.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with η hη
  exact (W_fn_eq f x_eq hconv hr_c hη).symm


lemma W_fn_mono_r (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Set.Ioc 0 c) (hr₂ : r₂ ∈ Set.Ioc 0 c) (h_le : r₁ ≤ r₂)
    {η : ℝ} (hη : 0 < η) :
    W_fn f x_eq r₁ η ≤ W_fn f x_eq r₂ η := by
  rw [W_fn_eq f x_eq hconv hr₁ hη, W_fn_eq f x_eq hconv hr₂ hη]
  have h_int1 := Tbar_intervalIntegrable_of_pos f x_eq hconv hr₁ (η / 2) η (half_pos hη) hη
  have h_int2 := Tbar_intervalIntegrable_of_pos f x_eq hconv hr₂ (η / 2) η (half_pos hη) hη
  refine add_le_add ?_ (div_le_div_of_nonneg_right h_le hη.le)
  gcongr
  refine intervalIntegral.integral_mono_on (half_le_self hη.le) h_int1 h_int2 ?_
  intro x hx
  exact Tbar_mono_r f x_eq hconv hr₁ hr₂ h_le (by linarith [hx.1])

lemma invFunOn_mono_r (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < a_α → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {a : ℝ} (ha : 0 < a) (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r₁ r₂ : ℝ} (hr₁ : r₁ ∈ Set.Ioc 0 a) (hr₂ : r₂ ∈ Set.Ioc 0 a) (h_le : r₁ ≤ r₂)
    {s : ℝ} (hs : 0 < s) :
    Function.invFunOn (W_fn f x_eq r₁) (Set.Ioi 0) s ≤ Function.invFunOn (W_fn f x_eq r₂)
      (Set.Ioi 0) s := by
  let U₁ := Function.invFunOn (W_fn f x_eq r₁) (Set.Ioi 0) s
  let U₂ := Function.invFunOn (W_fn f x_eq r₂) (Set.Ioi 0) s
  have hr1_c : r₁ ∈ Set.Ioc 0 c := ⟨hr₁.1, hr₁.2.trans ha_le_c⟩
  have hr2_c : r₂ ∈ Set.Ioc 0 c := ⟨hr₂.1, hr₂.2.trans ha_le_c⟩
  have hU₁_pos : 0 < U₁ := invFunOn_pos (W_fn_continuousOn f x_eq hconv hr1_c)
    (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα hr₁)
    (W_fn_tendsto_nhdsGT f x_eq hconv hr1_c) hs
  have hU₂_pos : 0 < U₂ := invFunOn_pos (W_fn_continuousOn f x_eq hconv hr2_c)
    (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα hr₂)
    (W_fn_tendsto_nhdsGT f x_eq hconv hr2_c) hs
  have hW₁ : W_fn f x_eq r₁ U₁ = s := apply_invFunOn_eq (W_fn_continuousOn f x_eq hconv hr1_c)
    (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα hr₁)
    (W_fn_tendsto_nhdsGT f x_eq hconv hr1_c) hs
  have hW₂ : W_fn f x_eq r₂ U₂ = s := apply_invFunOn_eq (W_fn_continuousOn f x_eq hconv hr2_c)
    (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα hr₂)
    (W_fn_tendsto_nhdsGT f x_eq hconv hr2_c) hs
  --Proof by contradiction: U₂ < U₁ implies s < s
  by_contra h_contra
  have h_lt : U₂ < U₁ := not_le.mp h_contra
  have hW_anti := W_fn_strictAntiOn f x_eq hconv hr1_c
  have h_strict : W_fn f x_eq r₁ U₁ < W_fn f x_eq r₁ U₂ := hW_anti hU₂_pos hU₁_pos h_lt
  have h_mono : W_fn f x_eq r₁ U₂ ≤ W_fn f x_eq r₂ U₂ :=
    W_fn_mono_r f x_eq hconv hr1_c hr2_c h_le hU₂_pos
  rw [hW₁] at h_strict
  linarith [h_strict, h_mono]


/-! ## U — time-decay function -/

lemma U_decay_bound (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {c : ℝ}
    (hconv : ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    {a_α b_α : ℝ} (α : ClassK a_α b_α)
    (hα_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < a_α → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {a : ℝ} (ha : 0 < a) (ha_le_c : a ≤ c) (ha_lt_aα : a < a_α)
    {r : ℝ} (hr : r ∈ Set.Ioc 0 a)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {φ : ℝ → ℝⁿ} (hφ : IsTrajectoryNA φ f)
    (h_init : ‖φ t₀ - x_eq‖ < r) {t : ℝ} (ht : t₀ < t) :
    ‖φ t - x_eq‖ ≤ Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) (t - t₀) := by
  let U_r := Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0)
  let s := t - t₀
  have hr_c : r ∈ Set.Ioc 0 c := ⟨hr.1, hr.2.trans ha_le_c⟩
  -- Fact 1: U_r maps into (0, ∞), so the radius is strictly positive
  have hU_pos : 0 < U_r s :=
    invFunOn_pos (W_fn_continuousOn f x_eq hconv hr_c)
      (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα hr)
      (W_fn_tendsto_nhdsGT f x_eq hconv hr_c) (sub_pos.mpr ht)
  -- Fact 2: U_r is the right-inverse of W, so W(U_r(s)) = s
  have h_WU : W_fn f x_eq r (U_r s) = s :=
    apply_invFunOn_eq (W_fn_continuousOn f x_eq hconv hr_c)
      (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα hr)
      (W_fn_tendsto_nhdsGT f x_eq hconv hr_c) (sub_pos.mpr ht)
  -- Use W_ge_Tbar to show s > Tbar
  have h_W_ge := W_ge_Tbar f x_eq hconv hr_c hU_pos
  have h_Tbar_lt_s : Tbar_fn f x_eq (U_r s) r < s := by
    calc Tbar_fn f x_eq (U_r s) r
      _ < Tbar_fn f x_eq (U_r s) r + r / (U_r s) := lt_add_of_pos_right _ (div_pos hr.1 hU_pos)
      _ ≤ W_fn f x_eq r (U_r s)                  := h_W_ge
      _ = s                                       := h_WU
  -- Because s > Tbar (the infimum of valid times), s is a valid time!
  have ht_eq : t₀ + s ≤ t := by change t₀ + (t - t₀) ≤ t; linarith
  have hne : (validTSet f x_eq (U_r s) r).Nonempty :=
    validTSet_nonempty f x_eq hconv hU_pos hr_c
  exact norm_le_of_Tbar_lt hne h_Tbar_lt_s ht₀ hφ h_init ht_eq

/-! ## Global KL helpers — W-function tools lifted to ClassKInfty -/

/-- Construct a `ClassK b (α b)` from a `ClassKInfty` by restriction to `[0, b]`. -/
private noncomputable def mk_ClassK_from_KInfty (α : ClassKInfty) {b : ℝ} (hb : 0 < b) :
    ClassK b (α.toFun b) :=
  ClassK.of_strictMono hb
    (α.map_zero ▸ α.strict_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hb.le) hb)
    α.toFun α.map_zero rfl
    (α.continuous.mono Set.Icc_subset_Ici_self)
    (α.strict_mono.mono Set.Icc_subset_Ici_self)

/-- Given a global class K∞ bound and global uniform convergence, the W-function inverse
    is strictly antitone on `(0, ∞)` for any radius `r > 0`. -/
lemma guas_invFunOn_strictAntiOn (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (α : ClassKInfty)
    (hGUC : ∀ η > 0, ∀ c > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    (h_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f → ∀ t : ℝ, t₀ ≤ t →
      ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {r : ℝ} (hr : 0 < r) :
    StrictAntiOn (Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0)) (Set.Ioi 0) := by
  have hconv := fun η hη => hGUC η hη (r + 1) (by linarith)
  let α_loc := mk_ClassK_from_KInfty α (show (0:ℝ) < r + 2 by linarith)
  have hα_loc : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < r + 2 → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α_loc.toFun ‖φ t₀ - x_eq‖ :=
    fun t₀ ht₀ φ hφ _ t ht => h_bound t₀ ht₀ φ hφ t ht
  exact strictAntiOn_invFunOn
    (W_fn_continuousOn f x_eq hconv ⟨hr, by linarith⟩)
    (W_fn_strictAntiOn f x_eq hconv ⟨hr, by linarith⟩)
    (W_fn_tendsto_atTop f x_eq hconv α_loc hα_loc (by linarith) le_rfl (by linarith)
      ⟨hr, by linarith⟩)
    (W_fn_tendsto_nhdsGT f x_eq hconv ⟨hr, by linarith⟩)

/-- Given a global class K∞ bound and global uniform convergence, the W-function inverse
    is positive for any `s > 0`. -/
lemma guas_invFunOn_pos (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (α : ClassKInfty)
    (hGUC : ∀ η > 0, ∀ c > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    (h_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f → ∀ t : ℝ, t₀ ≤ t →
      ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {r : ℝ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    0 < Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) s := by
  have hconv := fun η hη => hGUC η hη (r + 1) (by linarith)
  let α_loc := mk_ClassK_from_KInfty α (show (0:ℝ) < r + 2 by linarith)
  have hα_loc : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < r + 2 → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α_loc.toFun ‖φ t₀ - x_eq‖ :=
    fun t₀ ht₀ φ hφ _ t ht => h_bound t₀ ht₀ φ hφ t ht
  exact invFunOn_pos
    (W_fn_continuousOn f x_eq hconv ⟨hr, by linarith⟩)
    (W_fn_tendsto_atTop f x_eq hconv α_loc hα_loc (by linarith) le_rfl (by linarith)
      ⟨hr, by linarith⟩)
    (W_fn_tendsto_nhdsGT f x_eq hconv ⟨hr, by linarith⟩) hs

/-- Given a global class K∞ bound and global uniform convergence, the W-function inverse
    tends to `0` as `s → +∞`. -/
lemma guas_invFunOn_tendsto_zero (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (α : ClassKInfty)
    (hGUC : ∀ η > 0, ∀ c > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    (h_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f → ∀ t : ℝ, t₀ ≤ t →
      ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0)) Filter.atTop (nhds 0) := by
  have hconv := fun η hη => hGUC η hη (r + 1) (by linarith)
  let α_loc := mk_ClassK_from_KInfty α (show (0:ℝ) < r + 2 by linarith)
  have hα_loc : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < r + 2 → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α_loc.toFun ‖φ t₀ - x_eq‖ :=
    fun t₀ ht₀ φ hφ _ t ht => h_bound t₀ ht₀ φ hφ t ht
  exact invFunOn_tendsto_zero
    (W_fn_continuousOn f x_eq hconv ⟨hr, by linarith⟩)
    (W_fn_strictAntiOn f x_eq hconv ⟨hr, by linarith⟩)
    (W_fn_tendsto_atTop f x_eq hconv α_loc hα_loc (by linarith) le_rfl (by linarith)
      ⟨hr, by linarith⟩)
    (W_fn_tendsto_nhdsGT f x_eq hconv ⟨hr, by linarith⟩)

/-- Given a global class K∞ bound and global uniform convergence, a trajectory starting
    strictly inside the `r`-ball decays to within the W-function inverse at time `t - t₀`. -/
lemma guas_U_decay_bound (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (α : ClassKInfty)
    (hGUC : ∀ η > 0, ∀ c > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    (h_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f → ∀ t : ℝ, t₀ ≤ t →
      ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {r : ℝ} (hr : 0 < r) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {φ : ℝ → ℝⁿ} (hφ : IsTrajectoryNA φ f)
    (h_init : ‖φ t₀ - x_eq‖ < r) {t : ℝ} (ht : t₀ < t) :
    ‖φ t - x_eq‖ ≤ Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) (t - t₀) := by
  have hconv := fun η hη => hGUC η hη (r + 1) (by linarith)
  let α_loc := mk_ClassK_from_KInfty α (show (0:ℝ) < r + 2 by linarith)
  have hα_loc : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < r + 2 → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α_loc.toFun ‖φ t₀ - x_eq‖ :=
    fun t₀ ht₀ φ hφ _ t ht => h_bound t₀ ht₀ φ hφ t ht
  exact U_decay_bound f x_eq hconv α_loc hα_loc (by linarith) le_rfl (by linarith)
    ⟨hr, by linarith⟩ ht₀ hφ h_init ht

/-- Given a global class K∞ bound and global uniform convergence, the W-function inverse
    is monotone in the radius parameter. -/
lemma guas_invFunOn_mono_r (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (α : ClassKInfty)
    (hGUC : ∀ η > 0, ∀ c > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η)
    (h_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f → ∀ t : ℝ, t₀ ≤ t →
      ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖)
    {s : ℝ} (hs : 0 < s) :
    MonotoneOn (fun r => Function.invFunOn (W_fn f x_eq (r + 1)) (Set.Ioi 0) s) (Set.Ici 0) := by
  intro r₁ hr₁ r₂ hr₂ h_le
  have hr1_nn : 0 ≤ r₁ := hr₁
  have hr2_nn : 0 ≤ r₂ := hr₂
  have hconv := fun η hη => hGUC η hη (r₂ + 2) (by linarith)
  let α_loc := mk_ClassK_from_KInfty α (show (0:ℝ) < r₂ + 3 by linarith)
  have hα_loc : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
      ‖φ t₀ - x_eq‖ < r₂ + 3 → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α_loc.toFun ‖φ t₀ - x_eq‖ :=
    fun t₀ ht₀ φ hφ _ t ht => h_bound t₀ ht₀ φ hφ t ht
  exact invFunOn_mono_r f x_eq hconv α_loc hα_loc (by linarith) le_rfl (by linarith)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith) hs
