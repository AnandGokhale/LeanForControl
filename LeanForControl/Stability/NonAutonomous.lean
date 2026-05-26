import LeanForControl.Stability.DefsNonAutonomous
import LeanForControl.Stability.AsymptoticStabilityTools
import LeanForControl.Stability.classK
import LeanForControl.axioms

import Architect


open MeasureTheory




variable {n : ℕ}

/-!
# `Stability.NonAutonomous`

Comparison-function characterisations of stability for non-autonomous ODEs `ẋ = f(t, x)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.5.

## Main results

* **Lemma 4.5 (i)** (`uniformlyStableNA_iff_classK`): `UniformlyStableNA` iff there exist
  a class K function `α` and `c > 0` (independent of `t₀`) such that
  `‖x(t) - x_eq‖ ≤ α(‖x(t₀) - x_eq‖)` for all `t ≥ t₀ ≥ 0`, `‖x(t₀) - x_eq‖ < c`. (4.19)

* **Lemma 4.5 (ii)** (`uniformlyAsymptoticStableNA_iff_classKL`): `UniformlyAsymptoticStableNA`
  iff there exist a class KL function `β` and `c > 0` (independent of `t₀`) such that
  `‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t − t₀)` for all `t ≥ t₀ ≥ 0`, `‖x(t₀) - x_eq‖ < c`.
  (4.20)

* **Lemma 4.5 (iii)** (`globallyUniformlyAsymptoticStableNA_iff_classKL`):
  `GloballyUniformlyAsymptoticStableNA` iff the class KL bound (4.20) holds for every
  initial state (no restriction on `‖x(t₀) - x_eq‖`).
-/

open Set Filter Topology

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)



lemma uniformlyStable_implies_classK (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    (hUS : UniformlyStableNA f x_eq) :
    ∃ (a b : ℝ) (_ : 0 < a) (_ : 0 < b) (α : ClassK a b),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α.toFun (‖φ t₀ - x_eq‖) := by
  obtain ⟨δ₀, hδ₀, hUS_1⟩ := hUS 1 one_pos
  let a := δ₀ / 2
  have ha       : 0 < a   := half_pos hδ₀
  have ha_lt_δ₀ : a < δ₀  := half_lt_self hδ₀
  let reachable (r : ℝ) : Set ℝ :=
    {d | ∃ (φ : ℝ → ℝⁿ) (t₀ t : ℝ), 0 ≤ t₀ ∧ t₀ ≤ t ∧ IsTrajectoryNA φ f ∧
         ‖φ t₀ - x_eq‖ ≤ r ∧ d = ‖φ t - x_eq‖}
  let ω (r : ℝ) : ℝ := sSup (reachable r)
  -- Common bound: any reachable d ≤ 1 when the initial radius is ≤ a
  have hbdd_of_le : ∀ r ≤ a, BddAbove (reachable r) := fun r hr =>
    ⟨1, fun d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, heq⟩ =>
      heq ▸ le_of_lt (hUS_1 t₀ ht₀ φ hφ (h_init.trans_lt (hr.trans_lt ha_lt_δ₀)) t ht)⟩
  -- ω(0) = 0: stability at ε forces any ‖φ t₀ - x_eq‖ = 0 trajectory to stay at 0
  have hω_zero : ω 0 = 0 := by
    apply le_antisymm
    · refine Real.sSup_le ?_ le_rfl
      rintro d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩
      have h0 : ‖φ t₀ - x_eq‖ = 0 := le_antisymm h_init (norm_nonneg _)
      refine le_of_forall_pos_lt_add (fun ε hε => ?_)
      obtain ⟨δ, hδ, hUS_ε⟩ := hUS ε hε
      linarith [hUS_ε t₀ ht₀ φ hφ (h0 ▸ hδ) t ht]
    · rcases (reachable 0).eq_empty_or_nonempty with h | ⟨d, hd⟩
      · change 0 ≤ sSup (reachable 0); rw [h]; simp
      · obtain ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩ := hd
        exact (norm_nonneg _).trans
          (le_csSup (hbdd_of_le 0 ha.le) ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩)
  -- ω non-decreasing on [0, a]: reachable r₁ ⊆ reachable r₂ when r₁ ≤ r₂ ≤ a
  have hω_mono : ∀ s₁ s₂, 0 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ a → ω s₁ ≤ ω s₂ := by
    intro s₁ s₂ hs₁ hs₁₂ hs₂
    have hbdd₂ := hbdd_of_le s₂ hs₂
    rcases (reachable s₁).eq_empty_or_nonempty with h | hne
    · have hω₁ : ω s₁ = 0 := by change sSup (reachable s₁) = 0; rw [h]; simp
      rw [hω₁]; change 0 ≤ sSup (reachable s₂)
      rcases (reachable s₂).eq_empty_or_nonempty with h2 | ⟨d, hd⟩
      · rw [h2]; simp
      · obtain ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩ := hd
        exact (norm_nonneg _).trans (le_csSup hbdd₂ ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩)
    · refine csSup_le_csSup hbdd₂ hne ?_
      rintro d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩
      exact ⟨φ, t₀, t, ht₀, ht, hφ, h_init.trans hs₁₂, rfl⟩
  -- Class K majorant: exists_strictMono_upper_bound lifts ω to a strictly increasing bound
  obtain ⟨b, hb, α, hα_bound⟩ : ∃ (b : ℝ) (_ : 0 < b) (α : ClassK a b),
      ∀ r ∈ Set.Ico 0 a, ω r ≤ α.toFun r := by
    obtain ⟨g, b, hb, hg_zero, hg_a, hg_cont, hg_mono, hg_bound⟩ :=
      exists_strictMono_upper_bound a ha ω hω_zero hω_mono
    exact ⟨b, hb, ClassK.of_strictMono ha hb g hg_zero hg_a hg_cont hg_mono,
      fun r hr => hg_bound r hr.1 hr.2.le⟩
  -- Chain: ‖φ t - x_eq‖ ≤ ω(‖φ t₀ - x_eq‖) ≤ α(‖φ t₀ - x_eq‖)
  refine ⟨a, b, ha, hb, α, fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
  have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a := ⟨norm_nonneg _, h_init⟩
  exact (le_csSup (s := reachable (‖φ t₀ - x_eq‖)) (hbdd_of_le _ hr.2.le)
      ⟨φ, t₀, t, ht₀, ht, hφ, le_rfl, rfl⟩).trans (hα_bound _ hr)


/-- **Lemma 4.5 (i)**: The equilibrium `x_eq` is uniformly stable if and only if there exist
    a class K function `α` on `[0, c)` and a constant `c > 0` (independent of `t₀`) such that
    every trajectory with `‖φ t₀ - x_eq‖ < c` satisfies
    `‖φ t - x_eq‖ ≤ α(‖φ t₀ - x_eq‖)` for all `t ≥ t₀ ≥ 0`. -/
@[blueprint "lem:uniformlyStableNA-iff-classK"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(t,x)$ is
    \emph{uniformly stable} (\cref{def:uniformlyStableNA}) if and only if there exist a
    class $\mathcal{K}$ function $\alpha$ and a positive constant $c$, independent of
    $t_{0}$, such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \alpha(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|)
      \quad \forall\, t \ge t_{0} \ge 0,\; \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c.
    \] -/)]
theorem uniformlyStableNA_iff_classK (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    UniformlyStableNA f x_eq ↔
    ∃ (a b : ℝ) (_ : 0 < a) (_ : 0 < b) (α : ClassK a b),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α (‖φ t₀ - x_eq‖) := by
  refine ⟨uniformlyStable_implies_classK f x_eq, ?_⟩
  · rintro ⟨a, b, ha, hb, α, hα⟩ ε hε
    have h_cont := α.continuous 0 ⟨le_refl 0, α.ha⟩
    rw [Metric.continuousWithinAt_iff] at h_cont
    rcases h_cont ε hε with ⟨δ_c, hδ_c_pos, hδ_c⟩
    let δ := min (δ_c / 2) (a / 2)
    have hδ_pos : 0 < δ  := lt_min (half_pos hδ_c_pos) (half_pos ha)
    have hδ_a   : δ < a  := (min_le_right ..).trans_lt (half_lt_self ha)
    have hδ_lt  : δ < δ_c := (min_le_left ..).trans_lt (half_lt_self hδ_c_pos)
    refine ⟨δ, hδ_pos, fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
    have h_mono := α.strict_mono ⟨norm_nonneg _, h_init.trans hδ_a⟩ ⟨hδ_pos.le, hδ_a⟩ h_init
    have h_alpha := hδ_c ⟨hδ_pos.le, hδ_a⟩
      (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ_pos]; exact hδ_lt)
    rw [α.map_zero, Real.dist_eq, sub_zero] at h_alpha
    linarith [hα t₀ ht₀ φ hφ (h_init.trans hδ_a) t ht, h_mono, (abs_lt.mp h_alpha).2]


/-! ### UAS → ClassKL (forward direction, Sontag 1998) -/
lemma uniformlyAsymptoticStableNA_implies_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ)
    (hUAS : UniformlyAsymptoticStableNA f x_eq) :
    ∃ (a : ℝ) (_ : 0 < a) (β : ClassKL a),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β.toFun (‖φ t₀ - x_eq‖) (t - t₀) := by
  obtain ⟨hUS, c, hc_pos, hconv⟩ := hUAS
  obtain ⟨a_α, b_α, ha_α, hb_α, α, hα_bound⟩ := (uniformlyStableNA_iff_classK f x_eq).mp hUS
  let a := min (a_α / 2) c
  have ha : 0 < a := lt_min (by linarith) hc_pos
  have ha_le_aα2 : a ≤ a_α / 2 := min_le_left _ _
  have ha_le_c   : a ≤ c        := min_le_right _ _
  have ha_lt_aα  : a < a_α      := ha_le_aα2.trans_lt (half_lt_self ha_α)
  have ha_c : a ∈ Set.Ioc 0 c := ⟨ha, ha_le_c⟩
  have ha_a : a ∈ Set.Ioc 0 a := ⟨ha, le_refl a⟩
  have hU_strict_anti : StrictAntiOn (Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0)) (Set.Ioi 0) :=
    strictAntiOn_invFunOn (W_fn_continuousOn f x_eq hconv ha_c)
      (W_fn_strictAntiOn f x_eq hconv ha_c)
      (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα ha_a)
      (W_fn_tendsto_nhdsGT f x_eq hconv ha_c)
  have hU_pos : ∀ s > 0, 0 < Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0) s := fun _ hs =>
    invFunOn_pos (W_fn_continuousOn f x_eq hconv ha_c)
      (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα ha_a)
      (W_fn_tendsto_nhdsGT f x_eq hconv ha_c) hs
  have hU_tendsto : Filter.Tendsto (Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0))
      Filter.atTop (nhds 0) :=
    invFunOn_tendsto_zero (W_fn_continuousOn f x_eq hconv ha_c)
      (W_fn_strictAntiOn f x_eq hconv ha_c)
      (W_fn_tendsto_atTop f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα ha_a)
      (W_fn_tendsto_nhdsGT f x_eq hconv ha_c)
  let β_fun (r s : ℝ) : ℝ :=
    if h : s = 0 then α.toFun r
    else min (α.toFun r) (Real.sqrt (α.toFun r * Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0) s))
  refine ⟨a, ha, {
    ha       := ha
    toFun    := β_fun
    map_zero := by
      intro s hs; simp [β_fun, α.map_zero]
    nonneg := by
      intro r hr s hs
      dsimp [β_fun]
      have h_α : 0 ≤ α.toFun r := (α.maps_to ⟨hr.1, hr.2.trans ha_lt_aα⟩).1
      split_ifs with h_zero
      · exact h_α
      · exact le_min h_α (Real.sqrt_nonneg _)
    strict_mono_r := by
      intro s hs r₁ hr₁ r₂ hr₂ h_lt
      dsimp [β_fun]
      have hr₁_aα : r₁ ∈ Set.Ico 0 a_α := ⟨hr₁.1, hr₁.2.trans ha_lt_aα⟩
      have hr₂_aα : r₂ ∈ Set.Ico 0 a_α := ⟨hr₂.1, hr₂.2.trans ha_lt_aα⟩
      have h_α_lt : α.toFun r₁ < α.toFun r₂ := α.strict_mono hr₁_aα hr₂_aα h_lt
      by_cases h_zero : s = 0
      · simp [if_pos h_zero, h_α_lt]
      · simp only [if_neg h_zero]
        have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm h_zero)
        refine min_lt_min h_α_lt (Real.sqrt_lt_sqrt
          (mul_nonneg (α.maps_to hr₁_aα).1 (hU_pos s hs_pos).le)
          (mul_lt_mul_of_pos_right h_α_lt (hU_pos s hs_pos)))
    continuous_r  := by
      intro s hs
      dsimp [β_fun]
      -- Continuity: use Continuous.if for piecewise continuity
      split_ifs with h_zero
      · exact α.continuous.mono (Set.Ico_subset_Ico_right ha_lt_aα.le)
      · have h_cont_α := α.continuous.mono (Set.Ico_subset_Ico_right ha_lt_aα.le)
        fun_prop
    anti_s := by
      intro r hr s₁ hs₁ s₂ hs₂ h_le
      dsimp [β_fun]
      have h_α_nonneg : 0 ≤ α.toFun r := (α.maps_to ⟨hr.1, hr.2.trans ha_lt_aα⟩).1
      rcases (Set.mem_Ici.mp hs₁).eq_or_lt with rfl | hs₁_pos
      · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
        · exact le_refl _
        · simp [if_neg (ne_of_gt hs₂_pos)]
      · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
        · linarith
        · simp only [if_neg (ne_of_gt hs₁_pos), if_neg (ne_of_gt hs₂_pos)]
          gcongr
          exact hU_strict_anti.antitoneOn hs₁_pos hs₂_pos h_le
    tendsto_zero  := by
      intro r hr
      dsimp [β_fun]
      have h_α : 0 ≤ α.toFun r := (α.maps_to ⟨hr.1, hr.2.trans ha_lt_aα⟩).1
      have h_eq : (fun s ↦ if s = 0 then α.toFun r
        else min (α.toFun r) √(α.toFun r * Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0) s))
        =ᶠ[atTop]
        (fun s ↦ min (α.toFun r)
          √(α.toFun r * Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0) s)) := by
        filter_upwards [Filter.eventually_ne_atTop 0] with s hs
        exact if_neg hs
      apply Filter.Tendsto.congr' h_eq.symm
      refine squeeze_zero (fun s => le_min h_α (Real.sqrt_nonneg _))
        (fun s => min_le_right _ _) ?_
      have h_inner : Tendsto (fun s ↦ α.toFun r * Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0) s)
          atTop (𝓝 0) := by
        simpa using Filter.Tendsto.const_mul (α.toFun r) hU_tendsto
      have h_sqrt : Tendsto (fun x : ℝ ↦ Real.sqrt x) (𝓝 0) (𝓝 0) := by
        simpa [Real.sqrt_zero] using Real.continuous_sqrt.tendsto 0
      exact h_sqrt.comp h_inner
  }, ?_⟩
  intro t₀ ht₀ φ hφ h_init t ht
  have h_α : ‖φ t - x_eq‖ ≤ α.toFun (‖φ t₀ - x_eq‖) :=
    hα_bound t₀ ht₀ φ hφ (h_init.trans_le ha_lt_aα.le) t ht
  rcases ht.eq_or_lt with rfl | ht_strict
  · simp [β_fun, h_α]
  · have h_sub_ne : t - t₀ ≠ 0 := ne_of_gt (sub_pos.mpr ht_strict)
    dsimp [β_fun]
    simp only [if_neg h_sub_ne]
    have h_U : ‖φ t - x_eq‖ ≤ Function.invFunOn (W_fn f x_eq a) (Set.Ioi 0) (t - t₀) :=
      U_decay_bound f x_eq hconv α hα_bound ha ha_le_c ha_lt_aα ha_a ht₀ hφ h_init ht_strict
    refine le_min h_α ?_
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (φ t - x_eq), h_α, h_U])


/-- **Lemma 4.5 (ii)**: The equilibrium `x_eq` is uniformly asymptotically stable if and only
    if there exist a class KL function `β` on `[0, c)` and a constant `c > 0` (independent of
    `t₀`) such that every trajectory with `‖φ t₀ - x_eq‖ < c` satisfies
    `‖φ t - x_eq‖ ≤ β(‖φ t₀ - x_eq‖, t − t₀)` for all `t ≥ t₀ ≥ 0`. -/
@[blueprint "lem:uniformlyAsymptoticStableNA-iff-classKL"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{uniformly asymptotically
    stable} (\cref{def:uniformlyAsymptoticStableNA}) if and only if there exist a class
    $\mathcal{KL}$ function $\beta$ and a positive constant $c$, independent of $t_{0}$,
    such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \beta(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|,\, t - t_{0})
      \quad \forall\, t \ge t_{0} \ge 0,\; \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c.
    \] -/)]
theorem uniformlyAsymptoticStableNA_iff_classKL(f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    UniformlyAsymptoticStableNA f x_eq ↔
    ∃ (a : ℝ) (_ : 0 < a) (β : ClassKL a),
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < a →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β.toFun (‖φ t₀ - x_eq‖) (t - t₀) := by
  refine ⟨uniformlyAsymptoticStableNA_implies_classKL f x_eq, ?_⟩
  -- Backward: ∃ ClassKL bound → UAS
  rintro ⟨a, ha, β, hβ⟩
  have ha2 : (a / 2 : ℝ) ∈ Set.Ico 0 a := ⟨by positivity, half_lt_self ha⟩
  refine ⟨?_, a / 2, half_pos ha, ?_⟩
  · -- Uniform stability: continuity of β(·, 0) at 0 gives δ(ε)
    intro ε hε
    have h_cont := β.continuous_r 0 le_rfl 0 ⟨le_refl 0, ha⟩
    rw [Metric.continuousWithinAt_iff] at h_cont
    obtain ⟨δ, hδ_pos, hδ⟩ := h_cont ε hε
    refine ⟨min δ (a / 2), lt_min hδ_pos (half_pos ha),
            fun t₀ ht₀ φ hφ h_init t ht => ?_⟩
    have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a :=
      ⟨norm_nonneg _, h_init.trans ((min_le_right ..).trans_lt (half_lt_self ha))⟩
    have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
    have h2 := β.anti_s _ hr (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht_sub) ht_sub
    have hd : dist (‖φ t₀ - x_eq‖) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
      exact h_init.trans_le (min_le_left ..)
    have h3 := hδ hr hd
    rw [β.map_zero 0 le_rfl, Real.dist_eq, sub_zero,
        abs_of_nonneg (β.nonneg _ hr 0 le_rfl)] at h3
    linarith [hβ t₀ ht₀ φ hφ hr.2 t ht]
  · -- Convergence: β(a/2, s) → 0 as s → ∞ bounds all β(r, s) for r < a/2
    intro η hη
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
      (β.tendsto_zero (a / 2) ha2 (Iio_mem_nhds hη))
    refine ⟨max T 0 + 1, by linarith [le_max_right T (0:ℝ)], ?_⟩
    intro t₀ ht₀ φ hφ h_init t ht
    have ht_sub : 0 ≤ t - t₀ := by linarith [le_max_right T (0:ℝ)]
    have hr : ‖φ t₀ - x_eq‖ ∈ Set.Ico 0 a :=
      ⟨norm_nonneg _, h_init.trans (half_lt_self ha)⟩
    have h1 := hβ t₀ ht₀ φ hφ hr.2 t (by linarith)
    have h2 : β.toFun ‖φ t₀ - x_eq‖ (t - t₀) < β.toFun (a / 2) (t - t₀) :=
      β.strict_mono_r _ ht_sub hr ha2 h_init
    have h3 : β.toFun (a / 2) (t - t₀) ≤ β.toFun (a / 2) (max T 0) :=
      β.anti_s (a / 2) ha2 (Set.mem_Ici.mpr (le_max_right T 0))
        (Set.mem_Ici.mpr ht_sub) (by linarith [le_max_right T (0:ℝ)])
    have h4 : β.toFun (a / 2) (max T 0) < η := hT (max T 0) (le_max_left T 0)
    linarith




-- /-- **Lemma 4.5 (iii)**: The equilibrium `x_eq` is globally uniformly asymptotically stable
--     if and only if there exists a function `β : ℝ≥0 × ℝ≥0 → ℝ≥0` that is class K in the
--     first argument and decays to zero in the second (a global class KL bound), such that
--     `‖φ t - x_eq‖ ≤ β(‖φ t₀ - x_eq‖, t − t₀)` holds for **every** trajectory and every
--     `t ≥ t₀ ≥ 0`, with no restriction on the initial size `‖φ t₀ - x_eq‖`. -/
-- @[blueprint "lem:globallyUniformlyAsymptoticStableNA-iff-classKL"
--   (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{globally uniformly
--     asymptotically stable} (\cref{def:globallyUniformlyAsymptoticStableNA}) if and only
--     if there exists $\beta : [0,\infty) \times [0,\infty) \to [0,\infty)$ that is class
--     $\mathcal{K}$ in the first argument and, for each fixed $r \ge 0$, is decreasing to
--     $0$ as $s \to \infty$, such that
--     \[
--       \|\varphi(t) - x_{\mathrm{eq}}\| \le \beta(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|,
--              \, t - t_{0})
--       \quad \forall\, t \ge t_{0} \ge 0,
--     \]
--     with no restriction on the initial state $\varphi(t_{0})$. -/)]
theorem globallyUniformlyAsymptoticStableNA_iff_classKL (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) :
    GloballyUniformlyAsymptoticStableNA f x_eq ↔
    ∃ β : ℝ → ℝ → ℝ,
      (∀ s ≥ 0, β 0 s = 0) ∧
      (∀ s ≥ 0, ContinuousOn (fun r => β r s) (Set.Ici 0)) ∧
      (∀ s ≥ 0, StrictMonoOn (fun r => β r s) (Set.Ici 0)) ∧
      (Filter.Tendsto (fun r => β r 0) Filter.atTop Filter.atTop) ∧
      (∀ r ≥ 0, AntitoneOn (fun s => β r s) (Set.Ici 0)) ∧
      (∀ r ≥ 0, Filter.Tendsto (fun s => β r s) Filter.atTop (nhds 0)) ∧
      ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ β (‖φ t₀ - x_eq‖) (t - t₀) := by
  constructor
  · intro hGUAS
    obtain ⟨hGUS, hGUC⟩ := hGUAS
    let reachable (r : ℝ) : Set ℝ :=
      {d | ∃ (φ : ℝ → ℝⁿ) (t₀ t : ℝ), 0 ≤ t₀ ∧ t₀ ≤ t ∧ IsTrajectoryNA φ f ∧
           ‖φ t₀ - x_eq‖ ≤ r ∧ d = ‖φ t - x_eq‖}
    let ω (r : ℝ) : ℝ := sSup (reachable r)
    -- 2. Global Uniform Stability bounds the reachable set
    -- (This is where you use your δ(ε) → ∞ inverse argument)
    have h_gus_bound : ∀ r ≥ 0, ∃ M, ∀ φ : ℝ → ℝⁿ, ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t →
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ ≤ r → ‖φ t - x_eq‖ ≤ M := by
      intro r _
      obtain ⟨δ, hδ_pos, hδ_top, hδ_stab⟩ := hGUS
      -- δ(ε) → ∞, so eventually there exists some M > 0 where δ(M) > r
      have h_eventual : ∀ᶠ ε in Filter.atTop, 0 < ε ∧ r < δ ε :=
        (Filter.eventually_gt_atTop 0).and (hδ_top (Filter.Ioi_mem_atTop r))
      obtain ⟨M, hM_pos, hM_gt_r⟩ := h_eventual.exists
      refine ⟨M, fun φ t₀ t ht₀ ht hφ h_init => ?_⟩
      have h_init_lt : ‖φ t₀ - x_eq‖ < δ M := (by linarith)
      exact (hδ_stab M hM_pos t₀ ht₀ φ hφ h_init_lt t ht).le
    -- 3. Strict stability at the origin (starting at x_eq means staying at x_eq)
    have h_gus_zero : ∀ φ : ℝ → ℝⁿ, ∀ t₀ t : ℝ, 0 ≤ t₀ → t₀ ≤ t →
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ = 0 → ‖φ t - x_eq‖ = 0 := by
      intro φ t₀ t ht₀ ht hφ h_init
      obtain ⟨δ, hδ_pos, _, hδ_stab⟩ := hGUS
      apply le_antisymm _ (norm_nonneg _)
      -- ‖φ t - x_eq‖ < ε for every ε > 0, so it must be 0
      apply le_of_forall_pos_lt_add
      intro ε hε
      simp only [zero_add]
      have h_init_lt : ‖φ t₀ - x_eq‖ < δ ε := h_init.symm ▸ hδ_pos ε hε
      exact hδ_stab ε hε t₀ ht₀ φ hφ h_init_lt t ht
    have hbdd_of_le : ∀ r ≥ 0, BddAbove (reachable r) := fun r hr => by
      obtain ⟨M, hM⟩ := h_gus_bound r hr
      exact ⟨M, fun _ ⟨φ, t₀, t, ht₀, ht, hφ, h_init, heq⟩ => heq ▸ hM φ t₀ t ht₀ ht hφ h_init⟩
    have hω_zero : ω 0 = 0 := by
      dsimp [ω]
      by_cases h_empty : reachable 0 = ∅
      · rw [h_empty, Real.sSup_empty]
      · have h_nonempty : (reachable 0).Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
        have h_reach_zero : reachable 0 = {0} := by
          ext d
          constructor
          · rintro ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩
            exact h_gus_zero φ t₀ t ht₀ ht hφ (le_antisymm h_init (norm_nonneg _))
          · rintro rfl
            obtain ⟨_, φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩ := h_nonempty
            exact ⟨φ, t₀, t, ht₀, ht, hφ, h_init, (h_gus_zero φ t₀ t ht₀ ht hφ
              (le_antisymm h_init (norm_nonneg _))).symm⟩
        rw [h_reach_zero, csSup_singleton]
    have hω_mono : MonotoneOn ω (Set.Ici 0) := by
      intro r₁ hr₁ r₂ hr₂ h_le
      dsimp [ω]
      by_cases h_empty : reachable r₁ = ∅
      · rw [h_empty, Real.sSup_empty]
        by_cases h_empty2 : reachable r₂ = ∅
        · rw [h_empty2, Real.sSup_empty]
        · have h_nonempty2 : (reachable r₂).Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty2
          obtain ⟨d, hd⟩ := h_nonempty2
          obtain ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩ := hd
          have hd_mem : ‖φ t - x_eq‖ ∈ reachable r₂ := ⟨φ, t₀, t, ht₀, ht, hφ, h_init, rfl⟩
          exact (norm_nonneg _).trans (le_csSup (hbdd_of_le r₂ hr₂) hd_mem)
      · exact csSup_le_csSup (hbdd_of_le r₂ hr₂) (Set.nonempty_iff_ne_empty.mpr h_empty)
          fun d ⟨φ, t₀, t, ht₀, ht, hφ, h_init, heq⟩ =>
            ⟨φ, t₀, t, ht₀, ht, hφ, h_init.trans h_le, heq⟩
    obtain ⟨α, hα_bound⟩ := exists_classKInfty_upper_bound ω hω_zero hω_mono
    have h_global_α_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f →
        ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖ := by
      intro t₀ ht₀ φ hφ t ht
      have h_in_reach : ‖φ t - x_eq‖ ∈ reachable (‖φ t₀ - x_eq‖) := by
        dsimp [reachable]; exact ⟨φ, t₀, t, ht₀, ht, hφ, le_rfl, rfl⟩
      exact (le_csSup (hbdd_of_le _ (norm_nonneg _)) h_in_reach).trans
        (hα_bound _ (Set.mem_Ici.mpr (norm_nonneg _)))
    have hU_strict_anti : ∀ r > 0, StrictAntiOn (Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0))
        (Set.Ioi 0) :=
      fun r hr => guas_invFunOn_strictAntiOn f x_eq α hGUC h_global_α_bound hr
    have hU_pos : ∀ r > 0, ∀ s > 0, 0 < Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) s :=
      fun r hr s hs => guas_invFunOn_pos f x_eq α hGUC h_global_α_bound hr hs
    have hU_tendsto : ∀ r > 0, Filter.Tendsto (Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0))
        Filter.atTop (nhds 0) :=
      fun r hr => guas_invFunOn_tendsto_zero f x_eq α hGUC h_global_α_bound hr
    have hU_decay : ∀ r > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
        IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < r → ∀ t > t₀,
        ‖φ t - x_eq‖ ≤ Function.invFunOn (W_fn f x_eq r) (Set.Ioi 0) (t - t₀) :=
      fun r hr t₀ ht₀ φ hφ h_init t ht =>
        guas_U_decay_bound f x_eq α hGUC h_global_α_bound hr ht₀ hφ h_init ht
    have hU_mono_r : ∀ s > 0, MonotoneOn (fun r => Function.invFunOn (W_fn f x_eq (r + 1))
        (Set.Ioi 0) s) (Set.Ici 0) :=
      fun s hs => guas_invFunOn_mono_r f x_eq α hGUC h_global_α_bound hs
    let ψ (r s : ℝ) : ℝ :=
      if h : s = 0 then α.toFun r
      else min (α.toFun r) (Real.sqrt (α.toFun r * Function.invFunOn
        (W_fn f x_eq (r + 1)) (Set.Ioi 0) s))
    have hψ_nonneg : ∀ r ≥ 0, ∀ s ≥ 0, 0 ≤ ψ r s := by
      intro r hr s hs
      dsimp [ψ]
      split_ifs
      · exact α.maps_to hr
      · exact le_min (α.maps_to hr) (Real.sqrt_nonneg _)
    have hψ_zero : ∀ s ≥ 0, ψ 0 s = 0 := by
      intro s _
      dsimp [ψ]
      split_ifs with h_zero
      · exact α.map_zero
      · rw [α.map_zero, zero_mul, Real.sqrt_zero, min_self]
    have hψ_mono : ∀ s ≥ 0, MonotoneOn (fun r => ψ r s) (Set.Ici 0) := by
      intro s hs r₁ hr₁ r₂ hr₂ h_le
      dsimp [ψ]
      rcases eq_or_lt_of_le h_le with rfl | h_lt
      · exact le_rfl
      · have h_α_le : α.toFun r₁ ≤ α.toFun r₂ := le_of_lt (α.strict_mono hr₁ hr₂ h_lt)
        by_cases h_zero : s = 0
        · simp [if_pos h_zero, h_α_le]
        · simp only [if_neg h_zero]
          have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm h_zero)
          -- Apply our new global helper
          have h_U_le : Function.invFunOn (W_fn f x_eq (r₁ + 1)) (Set.Ioi 0) s ≤ Function.invFunOn
            (W_fn f x_eq (r₂ + 1)) (Set.Ioi 0) s :=
            hU_mono_r s hs_pos hr₁ hr₂ h_le
          refine min_le_min h_α_le ?_
          -- Branch to protect r₁ = 0
          rcases (Set.mem_Ici.mp hr₁).eq_or_lt with rfl | hr₁_pos
          · rw [α.map_zero, zero_mul, Real.sqrt_zero]
            exact Real.sqrt_nonneg _
          · -- When everything is strictly positive, nlinarith crushes the multiplication bound
            have h_U_nonneg : 0 ≤ Function.invFunOn (W_fn f x_eq (r₁ + 1)) (Set.Ioi 0) s :=
            le_of_lt (hU_pos (r₁ + 1) (by positivity) s hs_pos)
            -- Explicitly construct the A * B ≤ C * D bound
            apply Real.sqrt_le_sqrt
            gcongr
            exact α.maps_to (hr₂)
    have hψ_rtendsto : Filter.Tendsto (fun r => ψ r 0) Filter.atTop Filter.atTop := by
      have h_eq : (fun r => ψ r 0) = α.toFun := by ext r; dsimp [ψ]; simp
      rw [h_eq]
      exact α.tendsto_atTop
    have hψ_anti : ∀ r ≥ 0, AntitoneOn (fun s => ψ r s) (Set.Ici 0) := by
      intro r hr s₁ hs₁ s₂ hs₂ h_le
      dsimp [ψ]
      rcases eq_or_lt_of_le hr with rfl | hr_pos
      · simp [α.map_zero]
      · have h_α_pos : 0 < α.toFun r := by
          calc 0 = α.toFun 0 := α.map_zero.symm
            _ < α.toFun r := α.strict_mono (Set.mem_Ici.mpr (le_refl 0)) hr hr_pos
        rcases (Set.mem_Ici.mp hs₁).eq_or_lt with rfl | hs₁_pos
        · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
          · exact le_refl _
          · simp [if_neg (ne_of_gt hs₂_pos)]
        · rcases (Set.mem_Ici.mp hs₂).eq_or_lt with rfl | hs₂_pos
          · linarith
          · simp only [if_neg (ne_of_gt hs₁_pos), if_neg (ne_of_gt hs₂_pos)]
            gcongr
            exact (hU_strict_anti (r + 1) (by positivity)).antitoneOn hs₁_pos hs₂_pos h_le
    have hψ_tendsto : ∀ r ≥ 0, Filter.Tendsto (fun s => ψ r s) Filter.atTop (nhds 0) := by
      intro r hr
      dsimp [ψ]
      rcases eq_or_lt_of_le hr with rfl | hr_pos
      · -- r = 0 case
        simp [α.map_zero]
      · -- r > 0 case
        have h_α : 0 ≤ α.toFun r := by
          exact α.maps_to (hr)
        have h_eq : (fun s ↦ if s = 0 then α.toFun r
          else min (α.toFun r) √(α.toFun r * Function.invFunOn (W_fn f x_eq (r + 1)) (Set.Ioi 0) s))
          =ᶠ[Filter.atTop]
          (fun s ↦ min (α.toFun r) √(α.toFun r * Function.invFunOn (W_fn f x_eq (r + 1))
            (Set.Ioi 0) s)) := by
          filter_upwards [Filter.eventually_ne_atTop 0] with s hs
          exact if_neg hs
        apply Filter.Tendsto.congr' h_eq.symm
        refine squeeze_zero (fun s => le_min h_α (Real.sqrt_nonneg _))
          (fun s => min_le_right _ _) ?_
        have h_inner : Filter.Tendsto (fun s ↦ α.toFun r * Function.invFunOn (W_fn f x_eq (r + 1))
          (Set.Ioi 0) s) Filter.atTop (nhds 0) := by
          simpa using Filter.Tendsto.const_mul (α.toFun r) (hU_tendsto (r + 1) (by positivity))
        have h_sqrt : Filter.Tendsto (fun x : ℝ ↦ Real.sqrt x) (nhds 0) (nhds 0) := by
          simpa [Real.sqrt_zero] using Real.continuous_sqrt.tendsto 0
        exact h_sqrt.comp h_inner
    -- 3. PIPE IT THROUGH THE SMOOTHING AXIOM
    have hψ_cont : ContinuousWithinAt (fun r => ψ r 0) (Set.Ici 0) 0 := by
      have h : (fun r => ψ r 0) = α.toFun := funext fun r => by
        dsimp [ψ]; split_ifs with h
        · rfl
        · exact absurd rfl h
      rw [h]; exact α.continuous.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
    obtain ⟨β, hβ_upper_bound⟩ :=
      exists_classKL_upper_bound ψ hψ_nonneg hψ_zero hψ_mono hψ_anti hψ_tendsto
        hψ_cont
    -- K∞ in r propagates: ψ(r,0) ≤ β(r,0) and ψ(·,0) → ∞ forces β(·,0) → ∞
    have hβ_rtendsto : Filter.Tendsto (fun r => β.toFun r 0) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      have h := Filter.tendsto_atTop.mp hψ_rtendsto b
      filter_upwards [h, Filter.eventually_ge_atTop 0] with r hr h0r
      exact hr.trans (hβ_upper_bound r h0r 0 le_rfl)
    refine ⟨β.toFun, β.map_zero, β.continuous_r, β.strict_mono_r, hβ_rtendsto, β.anti_s,
            β.tendsto_zero, ?_⟩
    intro t₀ ht₀ φ hφ t ht
    have h_traj_ψ : ‖φ t - x_eq‖ ≤ ψ (‖φ t₀ - x_eq‖) (t - t₀) := by
      have h_α : ‖φ t - x_eq‖ ≤ α.toFun (‖φ t₀ - x_eq‖) := by
        have h_in_reach : ‖φ t - x_eq‖ ∈ reachable (‖φ t₀ - x_eq‖) := by
          dsimp [reachable]
          refine ⟨φ, t₀, t, ht₀, ht, hφ, le_rfl, rfl⟩
        have h_le_ω : ‖φ t - x_eq‖ ≤ ω (‖φ t₀ - x_eq‖) :=
          le_csSup (hbdd_of_le _ (norm_nonneg _)) h_in_reach
        exact h_le_ω.trans (hα_bound _ (norm_nonneg _))
      rcases ht.eq_or_lt with rfl | ht_strict
      · simp [ψ, h_α]
      · have h_sub_ne : t - t₀ ≠ 0 := ne_of_gt (sub_pos.mpr ht_strict)
        dsimp [ψ]
        simp only [if_neg h_sub_ne]
        rcases (norm_nonneg (φ t₀ - x_eq)).eq_or_lt with hr_zero | hr_pos
        · -- r = 0 case: The state never left the equilibrium!
          have hr_eq_zero : ‖φ t₀ - x_eq‖ = 0 := hr_zero.symm
          have h_α_zero : α.toFun (‖φ t₀ - x_eq‖) = 0 := by rw [hr_eq_zero, α.map_zero]
          have h_t_zero : ‖φ t - x_eq‖ = 0 := by linarith [h_α, h_α_zero, norm_nonneg (φ t - x_eq)]
          rw [h_t_zero]
          exact le_min (α.maps_to (Set.mem_Ici.mpr (norm_nonneg _))) ((Real.sqrt_nonneg _))
        · -- r > 0 case: The state decays! Apply the global decay helper.
          have h_U : ‖φ t - x_eq‖ ≤ Function.invFunOn (W_fn f x_eq (‖φ t₀ - x_eq‖ + 1))
            (Set.Ioi 0) (t - t₀) :=
            hU_decay (‖φ t₀ - x_eq‖ + 1) (by positivity) t₀ ht₀ φ hφ (by linarith) t ht_strict
          refine le_min h_α ?_
          rw [← Real.sqrt_sq (norm_nonneg _)]
          exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg (φ t - x_eq), h_α, h_U])
    exact h_traj_ψ.trans (hβ_upper_bound (‖φ t₀ - x_eq‖) (Set.mem_Ici.mpr (norm_nonneg _))
      (t - t₀) (Set.mem_Ici.mpr (sub_nonneg.mpr ht)))
  · -- Backward: ∃ Global ClassKL bound → GUAS
    rintro ⟨β, hβ_zero, hβ_cont, hβ_mono, hβ_rtendsto, hβ_anti, hβ_stendsto, hβ_bound⟩
    let α : ClassKInfty := ClassKInfty.of_strictMono (fun r => β r 0)
      (hβ_zero 0 le_rfl) (hβ_cont 0 le_rfl) (hβ_mono 0 le_rfl) hβ_rtendsto
    refine ⟨?_, ?_⟩ -- Split into Uniform Stability and Global Uniform Convergence
    · -- Global Uniform Stability (∃ δ, ...)
      -- We use α.invFun as our δ function!
      refine ⟨α.invFun, ?_, α.symm.tendsto_atTop, ?_⟩
      · -- Prove δ(ε) > 0 for ε > 0
        intro ε hε
        have h_zero : α.symm.toFun 0 = 0 := α.symm.map_zero
        have h_mono := α.symm.strict_mono (Set.mem_Ici.mpr (le_refl 0))
          (Set.mem_Ici.mpr (le_of_lt hε)) hε
        rwa [h_zero] at h_mono
      · -- Prove the trajectory stays within ε
        intro ε hε t₀ ht₀ φ hφ h_init t ht
        have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
        -- Decay over time: β(‖x₀‖, t - t₀) ≤ β(‖x₀‖, 0)
        have h_decay : β ‖φ t₀ - x_eq‖ (t - t₀) ≤ β ‖φ t₀ - x_eq‖ 0 :=
          hβ_anti ‖φ t₀ - x_eq‖ (Set.mem_Ici.mpr (norm_nonneg _))
            (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht_sub) ht_sub
        -- Monotonicity in space: β(‖x₀‖, 0) = α(‖x₀‖) < α(δ(ε)) = ε
        have h_alpha_mono : α ‖φ t₀ - x_eq‖ < α (α.invFun ε) :=
          α.strict_mono (Set.mem_Ici.mpr (norm_nonneg _))
            (α.symm.maps_to (Set.mem_Ici.mpr (le_of_lt hε))) h_init
        -- By definition of inverse, α(α.invFun(ε)) = ε
        have h_inv : α (α.invFun ε) = ε :=
          α.right_inv (Set.mem_Ici.mpr (le_of_lt hε))
        have h_traj := hβ_bound t₀ ht₀ φ hφ t ht
        calc ‖φ t - x_eq‖
          _ ≤ β ‖φ t₀ - x_eq‖ (t - t₀) := h_traj
          _ ≤ β ‖φ t₀ - x_eq‖ 0        := h_decay
          _ = α.toFun ‖φ t₀ - x_eq‖    := rfl
          _ < α.toFun (α.invFun ε)     := h_alpha_mono
          _ = ε                        := h_inv
    · -- Global Uniform Convergence
      intro η hη r hr_pos
      have hr_ici : r ∈ Set.Ici 0 := Set.mem_Ici.mpr hr_pos.le
      obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
        (hβ_stendsto r hr_ici (Iio_mem_nhds hη))
      refine ⟨max T 0 + 1, by linarith [le_max_right T (0:ℝ)], ?_⟩
      intro t₀ ht₀ φ hφ h_init t ht
      have ht_sub : 0 ≤ t - t₀ := by linarith [le_max_right T (0:ℝ)]
      have h_init_ici : ‖φ t₀ - x_eq‖ ∈ Set.Ici 0 := Set.mem_Ici.mpr (norm_nonneg _)
      have h1 := hβ_bound t₀ ht₀ φ hφ t (by linarith)
      -- Monotonicity bounds the initial state by r
      have h2 : β ‖φ t₀ - x_eq‖ (t - t₀) < β r (t - t₀) :=
        hβ_mono (t - t₀) ht_sub h_init_ici hr_ici h_init
      -- Decay over time ensures we fall below η
      have h3 : β r (t - t₀) ≤ β r (max T 0) :=
        hβ_anti r hr_ici (Set.mem_Ici.mpr (le_max_right T 0)) (Set.mem_Ici.mpr ht_sub)
        (by linarith [le_max_right T (0:ℝ)])
      have h4 : β r (max T 0) < η := hT (max T 0) (le_max_left T 0)
      linarith
