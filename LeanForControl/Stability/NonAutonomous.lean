import LeanForControl.Stability.DefsNonAutonomous
import LeanForControl.Stability.LyapunovBounds
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKL
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Stability.ClassKDecay
import LeanForControl.Dini.DiniDeriv
import LeanForControl.Stability.KLCharacterization

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

open Set Filter Topology Metric

/-! ## Chain rule for time-varying V along trajectories -/

lemma hasDerivAt_V_comp_traj_NA
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectoryNA φ f) (t : ℝ) :
    HasDerivAt (fun s => V s (φ s))
               (fderiv ℝ (Function.uncurry V) (t, φ t) (1, f t (φ t))) t := by
  have h_pair : HasDerivAt (fun s => (s, φ s)) (1, f t (φ t)) t :=
    (hasDerivAt_id t).prodMk (htraj t)
  exact (hV_diff (t, φ t)).hasFDerivAt.comp_hasDerivAt t h_pair

/-! ## V nonincreasing along trajectories -/

lemma V_NA_nonincreasing
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {φ : ℝ → ℝⁿ} (htraj : IsTrajectoryNA φ f)
    {a b : ℝ} (hab : a ≤ b)
    (hLie : ∀ t ∈ Set.Ioo a b,
        fderiv ℝ (Function.uncurry V) (t, φ t) (1, f t (φ t)) ≤ 0) :
    V b (φ b) ≤ V a (φ a) := by
  have hderiv : ∀ s, HasDerivAt (fun u => V u (φ u))
      (fderiv ℝ (Function.uncurry V) (s, φ s) (1, f s (φ s))) s :=
    fun s => hasDerivAt_V_comp_traj_NA hV_diff htraj s
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    (fun s hs => (hderiv s).differentiableAt.differentiableWithinAt)
    (fun s hs => by simp only [interior_Icc] at hs; rw [(hderiv s).deriv]; exact hLie s hs)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  exact hab

-- ─────────────────────────────────────────────────────────────────────────────
-- Helper: trajectories stay inside B_r when V starts below the threshold d
-- ─────────────────────────────────────────────────────────────────────────────

private lemma NA_ball_invariant
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ} {W₁ : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {r : ℝ} {b1 : ℝ} {α1 : ClassK r b1} {d : ℝ}
    (hd_Ico : d ∈ Set.Ico 0 b1) (h_invd_lt_r : α1.invFun d < r)
    (hW1_lb : ∀ x : ℝⁿ, ‖x‖ < r → α1.toFun ‖x‖ ≤ W₁ x)
    (hV_lb  : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r → W₁ x ≤ V t x)
    (hLie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
        fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ 0)
    {φ : ℝ → ℝⁿ} (hφ : IsTrajectoryNA φ f) {t₀ t : ℝ}
    (ht₀ : 0 ≤ t₀) (_ : t₀ ≤ t)
    (h_φt₀_lt_r : ‖φ t₀‖ < r) (h_Vt₀_lt_d : V t₀ (φ t₀) < d) :
    ∀ s : ℝ, t₀ ≤ s → s ≤ t → ‖φ s‖ < r := by
  have hφ_cont : Continuous φ :=
    continuous_iff_continuousAt.mpr fun s => (hφ s).differentiableAt.continuousAt
  have h_norm_cont : Continuous (fun s => ‖φ s‖) := continuous_norm.comp hφ_cont
  by_contra h_neg
  push Not at h_neg
  obtain ⟨s_bad, hs_lo, hs_hi, hs_bad⟩ := h_neg
  set E := {s ∈ Set.Icc t₀ s_bad | r ≤ ‖φ s‖}
  have hE_ne  : E.Nonempty := ⟨s_bad, ⟨hs_lo, le_rfl⟩, hs_bad⟩
  have hE_bdd : BddBelow E := ⟨t₀, fun s hs => hs.1.1⟩
  have hE_cl  : IsClosed E :=
    IsClosed.inter isClosed_Icc
      (isClosed_le continuous_const (continuous_norm.comp hφ_cont))
  set T_exit := sInf E
  have hT_mem  : T_exit ∈ E      := hE_cl.csInf_mem hE_ne hE_bdd
  have hT_lo   : t₀ ≤ T_exit    := hT_mem.1.1
  have hT_ge_r : r ≤ ‖φ T_exit‖ := hT_mem.2
  have hT_gt   : t₀ < T_exit := by
    rcases lt_or_eq_of_le hT_lo with h | h
    · exact h
    · exact absurd (h ▸ hT_ge_r) (not_le.mpr h_φt₀_lt_r)
  have h_pre : ∀ s ∈ Set.Ico t₀ T_exit, ‖φ s‖ < r := fun s ⟨hsl, hsh⟩ =>
    not_le.mp fun h =>
      absurd (csInf_le hE_bdd ⟨⟨hsl, hsh.le.trans hT_mem.1.2⟩, h⟩) (not_le.mpr hsh)
  have hT_le_r : ‖φ T_exit‖ ≤ r := by
    by_contra h_gt; push Not at h_gt
    obtain ⟨s, hs_mem, hs_eq⟩ := intermediate_value_Icc (le_of_lt hT_gt)
      h_norm_cont.continuousOn ⟨le_of_lt h_φt₀_lt_r, le_of_lt h_gt⟩
    change ‖φ s‖ = r at hs_eq
    have hs_E : s ∈ E := ⟨⟨hs_mem.1, hs_mem.2.trans hT_mem.1.2⟩, hs_eq.symm ▸ le_rfl⟩
    have hT_le_s : T_exit ≤ s := csInf_le hE_bdd hs_E
    have hs_lt_T : s < T_exit := by
      rcases eq_or_lt_of_le hs_mem.2 with rfl | h_lt
      · linarith [hs_eq, h_gt]
      · exact h_lt
    linarith
  have h_stay : ∀ s ∈ Set.Icc t₀ T_exit, ‖φ s‖ ≤ r := fun s hs => by
    rcases hs.2.eq_or_lt with rfl | h
    · exact hT_le_r
    · exact le_of_lt (h_pre s ⟨hs.1, h⟩)
  -- Find T₁ ∈ [t₀, T_exit) with ‖φ T₁‖ > α1.invFun d (V is still below d there)
  have h_near : ∃ T₁ ∈ Set.Ico t₀ T_exit, α1.invFun d < ‖φ T₁‖ := by
    by_contra h_all; push Not at h_all
    have hT_le_invd : ‖φ T_exit‖ ≤ α1.invFun d := by
      by_contra h; push Not at h
      have hcont := (continuous_norm.comp hφ_cont).continuousAt (x := T_exit)
      rw [Metric.continuousAt_iff] at hcont
      obtain ⟨δ, hδ_pos, hδ⟩ := hcont (‖φ T_exit‖ - α1.invFun d) (by linarith)
      set s := T_exit - min δ (T_exit - t₀) / 2
      have hs_ico : s ∈ Set.Ico t₀ T_exit := by
        constructor <;> simp only [s] <;>
          linarith [min_le_right δ (T_exit - t₀),
                    half_pos (lt_min hδ_pos (sub_pos.mpr hT_gt))]
      have hs_close : dist s T_exit < δ := by
        rw [Real.dist_eq]; simp only [s]
        rw [abs_of_neg (by linarith [half_pos (lt_min hδ_pos (sub_pos.mpr hT_gt))])]
        linarith [min_le_left δ (T_exit - t₀),
                  half_pos (lt_min hδ_pos (sub_pos.mpr hT_gt))]
      linarith [(abs_lt.mp (by simpa [Function.comp] using hδ hs_close)).1, h_all s hs_ico]
    linarith [h_invd_lt_r.trans_le hT_ge_r]
  obtain ⟨T₁, hT₁_ico, hT₁_gt⟩ := h_near
  have hT₁_lt_r : ‖φ T₁‖ < r := h_pre T₁ hT₁_ico
  have hV_T₁_dec : V T₁ (φ T₁) ≤ V t₀ (φ t₀) :=
    V_NA_nonincreasing hV_diff hφ hT₁_ico.1
      (fun s hs => hLie_nonpos s (ht₀.trans hs.1.le) (φ s)
                     (h_stay s ⟨hs.1.le, hs.2.le.trans hT₁_ico.2.le⟩))
  have h_W1_gt_d : d < W₁ (φ T₁) :=
    calc d = α1.toFun (α1.invFun d) := (α1.right_inv hd_Ico).symm
         _ < α1.toFun ‖φ T₁‖       := α1.strict_mono (α1.inv_maps_to hd_Ico)
                                        ⟨norm_nonneg _, hT₁_lt_r⟩ hT₁_gt
         _ ≤ W₁ (φ T₁)             := hW1_lb (φ T₁) hT₁_lt_r
  linarith [hV_lb T₁ (ht₀.trans hT₁_ico.1) (φ T₁) hT₁_lt_r.le, hV_T₁_dec]

-- ─────────────────────────────────────────────────────────────────────────────
-- Main theorem  (Khalil Theorem 4.8)
-- ─────────────────────────────────────────────────────────────────────────────

theorem lyapunov_uniformly_stable_NA [NeZero n]
    (f : ℝ → ℝⁿ → ℝⁿ) (r : ℝ) (hr : 0 < r)
    (V : ℝ → ℝⁿ → ℝ)
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    (W₁ W₂ : ℝⁿ → ℝ)
    (hW₁_cont : ContinuousOn W₁ (closedBall (0 : ℝⁿ) r))
    (hW₂_cont : ContinuousOn W₂ (closedBall (0 : ℝⁿ) r))
    (hW₁_zero : W₁ 0 = 0) (hW₂_zero : W₂ 0 = 0)
    (hW₁_pos : ∀ x ∈ closedBall (0 : ℝⁿ) r, x ≠ 0 → 0 < W₁ x)
    (hW₂_pos : ∀ x ∈ closedBall (0 : ℝⁿ) r, x ≠ 0 → 0 < W₂ x)
    (hV_sandwich : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
        W₁ x ≤ V t x ∧ V t x ≤ W₂ x)
    (hLie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
        fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ 0) :
    UniformlyStableNA f 0 := by
  -- ── Step 1: Lemma 4.3 — class K lower bound on W₁ ───────────────────────
  -- We only need α₁ as a lower bound; W₂ is handled via continuity directly.
  obtain ⟨b1_lower, b1_upper, α1, α1_upper, hW1_bounds⟩ :=
      LyapunovClassKBounds hr hW₁_cont hW₁_zero hW₁_pos
  obtain ⟨b2_lower, b2_upper, α2_lower, α2, hW2_bounds⟩ :=
      LyapunovClassKBounds hr hW₂_cont hW₂_zero hW₂_pos
  set d := min (b1_lower / 2) (b2_upper / 2)
  have hd_pos : 0 < d := lt_min (half_pos α1.hb) (half_pos α2.hb)
  have hd_lt_b1 : d < b1_lower := (min_le_left ..).trans_lt (half_lt_self α1.hb)
  have hd_lt_b2 : d < b2_upper := (min_le_right ..).trans_lt (half_lt_self α2.hb)
  set c := α2.invFun d
  have hc_pos : 0 < c := by
    calc 0 = α2.invFun 0 := α2.symm.map_zero.symm
         _ < α2.invFun d := α2.symm.strict_mono ⟨le_rfl, α2.hb⟩ ⟨hd_pos.le, hd_lt_b2⟩ hd_pos
  have hc_lt_r : c < r := (α2.inv_maps_to ⟨hd_pos.le, hd_lt_b2⟩).2
  -- The fundamental theorem of inverse functions: α₂(c) = d
  have h_α2_c : α2.toFun c = d := α2.right_inv ⟨hd_pos.le, hd_lt_b2⟩
  --let α2_res := α2.restrictTo hc_pos hc_lt_r h_α2_c
  let α2_res : ClassK c d :=
    ClassK.of_strictMono hc_pos hd_pos α2.toFun α2.map_zero h_α2_c
      (α2.continuous.mono (fun x hx => ⟨hx.1, hx.2.trans_lt hc_lt_r⟩))
      (α2.strict_mono.mono (fun x hx => ⟨hx.1, hx.2.trans_lt hc_lt_r⟩))
  let α1_inv_res := α1.symm.restrict hd_pos hd_lt_b1
  let α_comp : ClassK c (α1_inv_res.toFun d) :=
    ClassK.comp α1_inv_res α2_res
  -- Provide the composed function to the US characterization
  rw [uniformlyStableNA_iff_classK f 0]
  refine ⟨c, α1_inv_res.toFun d, hc_pos, α_comp.hb, α_comp, ?_⟩
  intro t₀ ht₀ φ hφ h_init t ht
  simp only [sub_zero] at h_init ⊢
  have h_φt₀_lt_r : ‖φ t₀‖ < r := h_init.trans hc_lt_r
  have h_Vt₀_lt_d : V t₀ (φ t₀) < d :=
    calc V t₀ (φ t₀)
        ≤ W₂ (φ t₀)          := (hV_sandwich t₀ ht₀ (φ t₀) h_φt₀_lt_r.le).2
      _ ≤ α2.toFun ‖φ t₀‖    := (hW2_bounds (φ t₀) h_φt₀_lt_r).2
      _ < α2.toFun c          := α2.strict_mono ⟨norm_nonneg _, h_φt₀_lt_r⟩
                                                ⟨hc_pos.le, hc_lt_r⟩ h_init
      _ = d                   := h_α2_c
  have hd_Ico : d ∈ Set.Ico 0 b1_lower := ⟨hd_pos.le, hd_lt_b1⟩
  have h_invd_lt_r : α1.invFun d < r := (α1.inv_maps_to hd_Ico).2
  have h_ball : ∀ s : ℝ, t₀ ≤ s → s ≤ t → ‖φ s‖ < r :=
    NA_ball_invariant hV_diff hd_Ico h_invd_lt_r
      (fun x hx => (hW1_bounds x hx).1)
      (fun t ht x hx => (hV_sandwich t ht x hx).1)
      hLie_nonpos hφ ht₀ ht h_φt₀_lt_r h_Vt₀_lt_d
  have h_φt_lt_r : ‖φ t‖ < r := h_ball t ht le_rfl
  have h_key : α1.toFun ‖φ t‖ ≤ α2.toFun ‖φ t₀‖ :=
    calc α1.toFun ‖φ t‖
        ≤ W₁ (φ t)         := (hW1_bounds (φ t) h_φt_lt_r).1
      _ ≤ V t (φ t)         := (hV_sandwich t (ht₀.trans ht) (φ t) h_φt_lt_r.le).1
      _ ≤ V t₀ (φ t₀)       := V_NA_nonincreasing hV_diff hφ ht
                                  (fun s hs => hLie_nonpos s (ht₀.trans hs.1.le) (φ s)
                                                 (h_ball s hs.1.le hs.2.le).le)
      _ ≤ W₂ (φ t₀)         := (hV_sandwich t₀ ht₀ (φ t₀) h_φt₀_lt_r.le).2
      _ ≤ α2.toFun ‖φ t₀‖   := (hW2_bounds (φ t₀) h_φt₀_lt_r).2
  have h_α2_Ico : α2.toFun ‖φ t₀‖ ∈ Set.Ico 0 b1_lower :=
    ⟨(α2.maps_to ⟨norm_nonneg _, h_φt₀_lt_r⟩).1,
     (α2.strict_mono ⟨norm_nonneg _, h_φt₀_lt_r⟩ ⟨hc_pos.le, hc_lt_r⟩ h_init).trans
       (h_α2_c ▸ hd_lt_b1)⟩
  have h_inv_bound : ‖φ t‖ ≤ α1.invFun (α2.toFun ‖φ t₀‖) := by
    by_contra h; push Not at h
    exact absurd h_key (not_le.mpr
      (calc α2.toFun ‖φ t₀‖
          = α1.toFun (α1.invFun (α2.toFun ‖φ t₀‖)) := (α1.right_inv h_α2_Ico).symm
        _ < α1.toFun ‖φ t‖ :=
            α1.strict_mono (α1.inv_maps_to h_α2_Ico) ⟨norm_nonneg _, h_φt_lt_r⟩ h))
  exact h_inv_bound


theorem lyapunov_uniformly_asymptotic_stable_NA [NeZero n]
    (f : ℝ → ℝⁿ → ℝⁿ) (r : ℝ) (hr : 0 < r)
    (V : ℝ → ℝⁿ → ℝ)
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    (W₁ W₂ W₃ : ℝⁿ → ℝ)
    (hW₁_cont : ContinuousOn W₁ (closedBall (0 : ℝⁿ) r))
    (hW₂_cont : ContinuousOn W₂ (closedBall (0 : ℝⁿ) r))
    (hW₃_cont : ContinuousOn W₃ (closedBall (0 : ℝⁿ) r))
    (hW₁_zero : W₁ 0 = 0) (hW₂_zero : W₂ 0 = 0) (hW₃_zero : W₃ 0 = 0)
    (hW₁_pos : ∀ x ∈ closedBall (0 : ℝⁿ) r, x ≠ 0 → 0 < W₁ x)
    (hW₂_pos : ∀ x ∈ closedBall (0 : ℝⁿ) r, x ≠ 0 → 0 < W₂ x)
    (hW₃_pos : ∀ x ∈ closedBall (0 : ℝⁿ) r, x ≠ 0 → 0 < W₃ x)
    (hV_sandwich : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
        W₁ x ≤ V t x ∧ V t x ≤ W₂ x)
    (hLie_bound : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
        fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ - W₃ x) :
    UniformlyAsymptoticStableNA f 0 := by
  -- ── Step 1: Extract Class K bounds ──────────────────────────────────────────
  obtain ⟨b1_lower, b1_upper, α1, α1_upper, hW1_bounds⟩ :=
      LyapunovClassKBounds hr hW₁_cont hW₁_zero hW₁_pos
  obtain ⟨b2_lower, b2_upper, α2_lower, α2, hW2_bounds⟩ :=
      LyapunovClassKBounds hr hW₂_cont hW₂_zero hW₂_pos
  -- (You can extract α3 here if your comparison lemma setup requires it)
  -- ── Step 2: Define d and c exactly as in Uniform Stability ────────────────
  set d := min (b1_lower / 2) (b2_upper / 2)
  have hd_pos : 0 < d := lt_min (half_pos α1.hb) (half_pos α2.hb)
  have hd_lt_b1 : d < b1_lower := (min_le_left ..).trans_lt (half_lt_self α1.hb)
  have hd_lt_b2 : d < b2_upper := (min_le_right ..).trans_lt (half_lt_self α2.hb)
  set c := α2.invFun d
  have hc_pos : 0 < c := by
    calc 0 = α2.invFun 0 := α2.symm.map_zero.symm
         _ < α2.invFun d := α2.symm.strict_mono ⟨le_rfl, α2.hb⟩ ⟨hd_pos.le, hd_lt_b2⟩ hd_pos
  have hc_lt_r : c < r := (α2.inv_maps_to ⟨hd_pos.le, hd_lt_b2⟩).2
  have h_α2_c : α2.toFun c = d := α2.right_inv ⟨hd_pos.le, hd_lt_b2⟩
  -- Downgrade hLie_bound to hLie_nonpos so we can reuse NA_ball_invariant
  have hLie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
      fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ 0 := by
    intro t ht x hx
    have hW3_nonneg : 0 ≤ W₃ x := by
      by_cases hx0 : x = 0
      · simp [hx0, hW₃_zero]
      · exact (hW₃_pos x (mem_closedBall_zero_iff.mpr hx) hx0).le
    linarith [hLie_bound t ht x hx]
  -- ── Step 3: The Comparison Lemma (Lemma 4.4) ──────────────────────────────
  -- Since V̇ ≤ -W₃(x) ≤ -α₃(α₂⁻¹(V)), standard comparison theory yields a Class KL function σ.
  obtain ⟨b3_lower, b3_upper, α3, α3_upper, hW3_bounds⟩ :=
      LyapunovClassKBounds hr hW₃_cont hW₃_zero hW₃_pos
  have h_α_comp : ∃ α_comp : ClassK d (α3.toFun c), ∀ y ∈ Set.Ico 0 d,
      α_comp.toFun y = α3.toFun (α2.invFun y) := by
    -- Restrict α2⁻¹ to the domain [0, d)
    let α2_inv_res := α2.symm.restrict hd_pos hd_lt_b2
    -- Restrict α3 to the domain [0, c)
    let α3_res := α3.restrict hc_pos hc_lt_r
    -- Cast α3_res so its domain syntactically matches the codomain of α2_inv_res.
    -- This works flawlessly because c is definitionally equal to α2.symm.toFun d!
    let α3_res' : ClassK (α2.symm.toFun d) (α3.toFun c) := α3_res
    -- Compose them directly
    let α_comp := ClassK.comp α3_res' α2_inv_res
    use α_comp
    intro y hy
    -- Because we just composed the functions without using Eq.rec (▸) casts,
    -- they are definitionally identical.
    exact rfl
  obtain ⟨α_comp, h_α_comp_eq⟩ := h_α_comp
  -- Shared helper: W₁ is non-negative on B(0, r)
  have hW1_nonneg_of : ∀ x : ℝⁿ, ‖x‖ ≤ r → 0 ≤ W₁ x := fun x hx => by
    by_cases hx0 : x = 0
    · simp [hx0, hW₁_zero]
    · exact (hW₁_pos x (mem_closedBall_zero_iff.mpr hx) hx0).le
  -- Get the comparison KL function σ (ODE infrastructure hidden in classK_dini_bound)
  obtain ⟨σ, hσ_zero, hσ_general⟩ := classK_dini_bound α_comp
  -- ── Trajectory bound: V(t, φ(t)) ≤ σ(V(t₀, φ(t₀)), t − t₀) ─────────────────
  have hσ_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀‖ < c → ∀ t : ℝ, t₀ ≤ t →
      V t (φ t) ≤ σ.toFun (V t₀ (φ t₀)) (t - t₀) := by
    intro t₀ ht₀ φ hφ h_init t ht
    have h_Vt₀_lt_d' : V t₀ (φ t₀) < d :=
      calc V t₀ (φ t₀)
          ≤ W₂ (φ t₀)       := (hV_sandwich t₀ ht₀ (φ t₀) (h_init.trans hc_lt_r).le).2
        _ ≤ α2.toFun ‖φ t₀‖ := (hW2_bounds (φ t₀) (h_init.trans hc_lt_r)).2
        _ < α2.toFun c      := α2.strict_mono ⟨norm_nonneg _, h_init.trans hc_lt_r⟩
                                 ⟨hc_pos.le, hc_lt_r⟩ h_init
        _ = d               := h_α2_c
    have h_φs_lt_r : ∀ s ∈ Set.Icc t₀ t, ‖φ s‖ < r := fun s hs =>
      NA_ball_invariant hV_diff ⟨hd_pos.le, hd_lt_b1⟩
        ((α1.inv_maps_to ⟨hd_pos.le, hd_lt_b1⟩).2)
        (fun x hx => (hW1_bounds x hx).1)
        (fun t' ht' x hx => (hV_sandwich t' ht' x hx).1)
        hLie_nonpos hφ ht₀ ht (h_init.trans hc_lt_r) h_Vt₀_lt_d'
        s hs.1 hs.2
    have hV_nonneg_t₀ : 0 ≤ V t₀ (φ t₀) :=
      (hW1_nonneg_of (φ t₀) (h_init.trans hc_lt_r).le).trans
        (hV_sandwich t₀ ht₀ (φ t₀) (h_init.trans hc_lt_r).le).1
    have hV_Ico_t₀ : V t₀ (φ t₀) ∈ Set.Ico 0 d := ⟨hV_nonneg_t₀, h_Vt₀_lt_d'⟩
    -- V stays in [0, d) along the trajectory (needed by classK_dini_bound)
    have hv_range : ∀ s ∈ Set.Ico t₀ t, V s (φ s) ∈ Set.Ico 0 d := fun s hs => by
      have h_φs_r  := h_φs_lt_r s ⟨hs.1, hs.2.le⟩
      have hV_nn   := (hW1_nonneg_of (φ s) h_φs_r.le).trans
        (hV_sandwich s (ht₀.trans hs.1) (φ s) h_φs_r.le).1
      have hV_lt_d :=
        (V_NA_nonincreasing hV_diff hφ hs.1
          (fun t' ht' => hLie_nonpos t' (ht₀.trans ht'.1.le) (φ t')
            (h_φs_lt_r t' ⟨ht'.1.le, (ht'.2.trans hs.2).le⟩).le)).trans_lt h_Vt₀_lt_d'
      exact ⟨hV_nn, hV_lt_d⟩
    -- KEY CONTROL THEORY: D⁺(V(·, φ(·)))(s) ≤ −α_comp(V(s, φ(s)))
    -- Chain: V̇ ≤ −W₃(φ s) ≤ −α₃(‖φ s‖) ≤ −α₃(α₂⁻¹(V(s, φ(s)))) = −α_comp(V(s, φ(s)))
    have hDv : ∀ s ∈ Set.Ico t₀ t,
        D⁺ (fun s => V s (φ s)) s ≤ -α_comp.toFun (V s (φ s)) := by
      intro s hs
      rw [diniDerivRight_of_hasDerivWithinAt
            (hasDerivAt_V_comp_traj_NA hV_diff hφ s).hasDerivWithinAt]
      have h_Lie    := hLie_bound s (ht₀.trans hs.1) (φ s) (h_φs_lt_r s ⟨hs.1, hs.2.le⟩).le
      have h_φs_r   := h_φs_lt_r s ⟨hs.1, hs.2.le⟩
      have h1       : α3.toFun ‖φ s‖ ≤ W₃ (φ s) := (hW3_bounds (φ s) h_φs_r).1
      have h2       : V s (φ s) ≤ α2.toFun ‖φ s‖ :=
        (hV_sandwich s (ht₀.trans hs.1) (φ s) h_φs_r.le).2.trans (hW2_bounds (φ s) h_φs_r).2
      have hV_Ico   : V s (φ s) ∈ Set.Ico 0 d := hv_range s hs
      have hV_in_b2 : V s (φ s) ∈ Set.Ico 0 b2_upper := ⟨hV_Ico.1, hV_Ico.2.trans hd_lt_b2⟩
      calc fderiv ℝ (Function.uncurry V) (s, φ s) (1, f s (φ s))
          ≤ -W₃ (φ s)                 := h_Lie
        _ ≤ -α3.toFun ‖φ s‖           := neg_le_neg h1
        _ ≤ -α_comp.toFun (V s (φ s)) := neg_le_neg (by
              rw [h_α_comp_eq (V s (φ s)) hV_Ico]
              exact α3.strict_mono.monotoneOn (α2.inv_maps_to hV_in_b2)
                ⟨norm_nonneg _, h_φs_r⟩
                (calc α2.symm.toFun (V s (φ s))
                    ≤ α2.symm.toFun (α2.toFun ‖φ s‖) :=
                        α2.symm.strict_mono.monotoneOn hV_in_b2
                          (α2.maps_to ⟨norm_nonneg _, h_φs_r⟩) h2
                  _ = ‖φ s‖ := α2.left_inv ⟨norm_nonneg _, h_φs_r⟩))
    -- Difference quotients are bounded (from HasDerivAt)
    have hv_bdd : ∀ s ∈ Set.Ico t₀ t,
        IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (V (s + h) (φ (s + h)) - V s (φ s)) / h) := by
      intro s _
      have h_deriv := hasDerivAt_V_comp_traj_NA hV_diff hφ s
      apply h_deriv.tendsto_slope_zero_right.isBoundedUnder_le.mono_le
      filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      simp only [smul_eq_mul, div_eq_mul_inv, mul_comm, le_refl]
    -- Apply the comparison wrapper
    exact hσ_general ht (fun s => V s (φ s))
      (hV_diff.continuous.comp (continuous_id.prodMk
        (continuous_iff_continuousAt.mpr fun s => (hφ s).differentiableAt.continuousAt)))
      hV_Ico_t₀ hv_range hDv hv_bdd
  -- ── Step 4: Construct β(r, s) = α₁⁻¹(σ(α₂(r), s)) ─────────────────────────
  -- Since your ClassKL.comp_left only takes ClassKInfty, we assert the existence
  -- of the composed KL bound manually here for you to construct.
  have h_beta : ∃ β : ClassKL c, ∀ r ∈ Set.Ico 0 c, ∀ s ≥ 0,
      α1.symm.toFun (σ.toFun (α2.toFun r) s) ≤ β.toFun r s := by
    set inner := σ.comp_right (α2.restrictTo hc_pos hc_lt_r h_α2_c)
    have h_inner_eq : ∀ r_val s, inner.toFun r_val s = σ.toFun (α2.toFun r_val) s := by
      intro r_val s
      -- A generic lemma to strip the `Eq.rec` cast away from `.toFun`
      have h_cast : ∀ {e} (h : α2.toFun c = e),
          (α2.restrictTo hc_pos hc_lt_r h).toFun r_val = α2.toFun r_val := by
        intro e h
        cases h
        rfl
      exact congrArg (fun x => σ.toFun x s) (h_cast h_α2_c)
    have h_range : ∀ r_val ∈ Set.Ico 0 c, ∀ s ≥ 0, inner.toFun r_val s < b1_lower := by
      intro r_val hr_val s hs
      have hα2r : α2.toFun r_val ∈ Set.Ico 0 d := by
        -- Step 1: Prove domain memberships for the global radius `r`
        have hr_in : r_val ∈ Set.Ico 0 r := ⟨hr_val.1, hr_val.2.trans hc_lt_r⟩
        have hc_in : c ∈ Set.Ico 0 r := ⟨hc_pos.le, hc_lt_r⟩
        -- Step 2: Use `maps_to` for the lower bound, and `strict_mono`
        exact ⟨(α2.maps_to hr_in).1, h_α2_c ▸ α2.strict_mono hr_in hc_in hr_val.2⟩
      calc inner.toFun r_val s
          = σ.toFun (α2.toFun r_val) s := h_inner_eq r_val s
        _ ≤ σ.toFun (α2.toFun r_val) 0 :=
            σ.anti_s _ hα2r (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
        _ ≤ α2.toFun r_val := hσ_zero _ hα2r
        _ < d := hα2r.2
        _ < b1_lower := hd_lt_b1
    exact ⟨inner.comp_left_K α1.symm h_range, fun r_val _ s _ => le_of_eq (by
      exact congrArg α1.symm.toFun (h_inner_eq r_val s).symm
    )⟩
  obtain ⟨β, hβ_bound⟩ := h_beta
  -- ── Step 5: Unpack UAS Definition and Apply ───────────────────────────────
  rw [uniformlyAsymptoticStableNA_iff_classKL f 0]
  use c, hc_pos, β
  intro t₀ ht₀ φ hφ h_init t ht
  simp only [sub_zero] at h_init ⊢
  have h_φt₀_lt_r : ‖φ t₀‖ < r := h_init.trans hc_lt_r
  have h_Vt₀_lt_d : V t₀ (φ t₀) < d :=
    calc V t₀ (φ t₀)
        ≤ W₂ (φ t₀)          := (hV_sandwich t₀ ht₀ (φ t₀) h_φt₀_lt_r.le).2
      _ ≤ α2.toFun ‖φ t₀‖    := (hW2_bounds (φ t₀) h_φt₀_lt_r).2
      _ < α2.toFun c         := α2.strict_mono
                                  ⟨norm_nonneg _, h_init.trans hc_lt_r⟩
                                  ⟨hc_pos.le, hc_lt_r⟩
                                  h_init
      _ = d                  := h_α2_c
  -- Prove it never leaves the ball so h_comparison is valid
  have h_ball : ∀ s : ℝ, t₀ ≤ s → s ≤ t → ‖φ s‖ < r :=
    NA_ball_invariant hV_diff ⟨hd_pos.le, hd_lt_b1⟩ ((α1.inv_maps_to ⟨hd_pos.le, hd_lt_b1⟩).2)
      (fun x hx => (hW1_bounds x hx).1)
      (fun s hs x hx => (hV_sandwich s hs x hx).1)
      hLie_nonpos hφ ht₀ ht h_φt₀_lt_r h_Vt₀_lt_d
  have h_φt_lt_r : ‖φ t‖ < r := h_ball t ht le_rfl
  have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hV_t0_Ico : V t₀ (φ t₀) ∈ Set.Ico 0 d :=
    ⟨(hW1_nonneg_of (φ t₀) h_φt₀_lt_r.le).trans
       (hV_sandwich t₀ ht₀ (φ t₀) h_φt₀_lt_r.le).1,
     h_Vt₀_lt_d⟩
  have h_α2_t0_Ico : α2.toFun ‖φ t₀‖ ∈ Set.Ico 0 d :=
    ⟨(α2.maps_to ⟨norm_nonneg _, h_φt₀_lt_r⟩).1,
     (α2.strict_mono ⟨norm_nonneg _, h_φt₀_lt_r⟩ ⟨hc_pos.le, hc_lt_r⟩ h_init).trans_eq h_α2_c⟩
  have h_V_le_α2 : V t₀ (φ t₀) ≤ α2.toFun ‖φ t₀‖ :=
    (hV_sandwich t₀ ht₀ (φ t₀) h_φt₀_lt_r.le).2.trans (hW2_bounds (φ t₀) h_φt₀_lt_r).2
  -- The Core Inequality Chain
  have h_chain : α1.toFun ‖φ t‖ ≤ σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) :=
    calc α1.toFun ‖φ t‖
      _ ≤ W₁ (φ t) := (hW1_bounds (φ t) h_φt_lt_r).1
      _ ≤ V t (φ t) := (hV_sandwich t (ht₀.trans ht) (φ t) h_φt_lt_r.le).1
      _ ≤ σ.toFun (V t₀ (φ t₀)) (t - t₀) := hσ_bound t₀ ht₀ φ hφ h_init t ht
      _ ≤ σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) :=
            (σ.strict_mono_r (t - t₀) ht_sub).monotoneOn hV_t0_Ico h_α2_t0_Ico h_V_le_α2
  -- Invert α1 and apply β
  have h_left_in : α1.toFun ‖φ t‖ ∈ Set.Ico 0 b1_lower := α1.maps_to ⟨norm_nonneg _, h_φt_lt_r⟩
  have h_right_in : σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) ∈ Set.Ico 0 b1_lower := by
    refine ⟨σ.nonneg (α2.toFun ‖φ t₀‖) h_α2_t0_Ico (t - t₀) ht_sub, ?_⟩
    have h_decay := σ.anti_s (α2.toFun ‖φ t₀‖) h_α2_t0_Ico
        (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht_sub) ht_sub
    calc σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀)
      _ ≤ σ.toFun (α2.toFun ‖φ t₀‖) 0 := h_decay
      _ ≤ α2.toFun ‖φ t₀‖ := hσ_zero (α2.toFun ‖φ t₀‖) h_α2_t0_Ico
      _ < d               := h_α2_t0_Ico.2
      _ < b1_lower        := hd_lt_b1
  have h_inv_bound := α1.symm.strict_mono.monotoneOn h_left_in h_right_in h_chain
  change α1.invFun (α1.toFun ‖φ t‖) ≤ α1.invFun (σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀)) at h_inv_bound
  have h_beta_eval : α1.invFun (σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀)) ≤ β.toFun ‖φ t₀‖ (t - t₀) :=
    hβ_bound ‖φ t₀‖ ⟨norm_nonneg _, h_init⟩ (t - t₀) ht_sub
  have:=  h_inv_bound.trans h_beta_eval
  rwa [α1.left_inv ⟨norm_nonneg _, h_φt_lt_r⟩] at this
