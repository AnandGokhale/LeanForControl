import LeanForControl.Stability.DefsNonAutonomous
import LeanForControl.Stability.LyapunovBounds
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKL
import LeanForControl.Comparison.ClassKInfty
import LeanForControl.Stability.ClassKDecay
import LeanForControl.Analysis.DiniDeriv
import LeanForControl.Stability.KLCharacterization

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Architect

/-!
# `Stability.NonAutonomous`

Lyapunov's stability theorems for time-varying systems `ẋ = f(t, x)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorems 4.8 and 4.9.

## Main results

* `lyapunov_uniformly_stable_NA` — a time-varying `V` sandwiched between two positive-definite
  functions of the state alone, with `V̇ ≤ 0`, gives uniform stability.
* `lyapunov_uniformly_asymptotic_stable_NA` — strengthening `V̇ ≤ 0` to `V̇ ≤ −W₃` gives uniform
  asymptotic stability.

The sandwich `W₁(x) ≤ V(t,x) ≤ W₂(x)` is what makes the conclusions *uniform* in `t₀`: it is
the time-varying analogue of positive definiteness, and without it a `V` could flatten out as
`t → ∞` and buy no uniform estimate.
-/

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

open Set Filter Topology Metric

/-! ## Chain rule for time-varying V along trajectories -/

/-- Chain rule for a time-varying `V` along a trajectory: the total derivative of
`t ↦ V t (φ t)` pairs the explicit time dependence with the state dependence, giving
`DV(t, φ t)[(1, f t (φ t))]`. -/
@[blueprint "lem:hasDerivAt-V-comp-traj-NA"
  (title := "Chain rule for a time-varying $V$")
  (latexEnv := "lemma")
  (statement := /-- Let $V : \mathbb{R} \times \mathbb{R}^{n} \to \mathbb{R}$ be
    differentiable and let $\varphi$ be a trajectory of $\dot{x} = f(t,x)$ on
    $[t_{0},\infty)$ (\cref{def:isTrajectoryNA}).  Then for $t > t_{0}$,
    \[
      \frac{d}{dt}\,V(t, \varphi(t)) = DV(t, \varphi(t))\,[\,(1,\, f(t, \varphi(t)))\,].
    \]
    The first slot of the derivative picks up the explicit time dependence of $V$, which is what
    distinguishes the non-autonomous Lie derivative from the autonomous one. -/)]
lemma hasDerivAt_V_comp_traj_NA
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {φ : ℝ → ℝⁿ} {t₀ : ℝ} (htraj : IsTrajectoryNA φ f t₀) {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (fun s => V s (φ s))
               (fderiv ℝ (Function.uncurry V) (t, φ t) (1, f t (φ t))) t := by
  have hφd : HasDerivAt φ (f t (φ t)) t :=
    (htraj t (Set.mem_Ici.mpr ht.le)).hasDerivAt (Ici_mem_nhds ht)
  have h_pair : HasDerivAt (fun s => (s, φ s)) (1, f t (φ t)) t :=
    (hasDerivAt_id t).prodMk hφd
  exact (hV_diff (t, φ t)).hasFDerivAt.comp_hasDerivAt t h_pair

/-- The chain rule at the left endpoint of the solution's interval, where only a
one-sided derivative exists. This is the form the Dini-derivative machinery consumes. -/
private lemma hasDerivWithinAt_V_comp_traj_NA
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {φ : ℝ → ℝⁿ} {t₀ : ℝ} (htraj : IsTrajectoryNA φ f t₀) {t : ℝ} (ht : t₀ ≤ t) :
    HasDerivWithinAt (fun s => V s (φ s))
      (fderiv ℝ (Function.uncurry V) (t, φ t) (1, f t (φ t))) (Set.Ici t) t := by
  have hφd : HasDerivWithinAt φ (f t (φ t)) (Set.Ici t) t :=
    (htraj t (Set.mem_Ici.mpr ht)).mono (Set.Ici_subset_Ici.mpr ht)
  have h_pair : HasDerivWithinAt (fun s => (s, φ s)) (1, f t (φ t)) (Set.Ici t) t :=
    (hasDerivWithinAt_id t _).prodMk hφd
  exact (hV_diff (t, φ t)).hasFDerivAt.comp_hasDerivWithinAt t h_pair

/-! ## V nonincreasing along trajectories -/

/-- If `V̇ = DV(t, φ t)[(1, f t (φ t))] ≤ 0` on `(a, b)`, then `V` is nonincreasing along the
trajectory between `a` and `b`: `V(b, φ b) ≤ V(a, φ a)`.  This is the mean value theorem
applied to `t ↦ V(t, φ t)`, which is differentiable by the chain rule above. -/
private lemma V_NA_nonincreasing
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {φ : ℝ → ℝⁿ} {t₀ : ℝ} (htraj : IsTrajectoryNA φ f t₀)
    {a b : ℝ} (ht₀a : t₀ ≤ a) (hab : a ≤ b)
    (hLie : ∀ t ∈ Set.Ioo a b,
        fderiv ℝ (Function.uncurry V) (t, φ t) (1, f t (φ t)) ≤ 0) :
    V b (φ b) ≤ V a (φ a) := by
  have hsub : Set.Icc a b ⊆ Set.Ici t₀ := fun s hs => Set.mem_Ici.mpr (ht₀a.trans hs.1)
  have hderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt (fun u => V u (φ u))
      (fderiv ℝ (Function.uncurry V) (s, φ s) (1, f s (φ s))) s :=
    fun s hs => hasDerivAt_V_comp_traj_NA hV_diff htraj (lt_of_le_of_lt ht₀a hs.1)
  have hcont : ContinuousOn (fun u => V u (φ u)) (Set.Icc a b) :=
    hV_diff.continuous.comp_continuousOn
      (continuousOn_id.prodMk (htraj.continuousOn.mono hsub))
  -- Not an instance of `antitoneOn_V_comp_traj`: `V` is time-varying here, so the derivative is
  -- `fderiv (uncurry V) (t, φ t) (1, f t (φ t))` rather than `fderiv V (φ t) (f (φ t))`.
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont
    (fun s hs => by
      rw [interior_Icc] at hs
      exact (hderiv s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => by
      rw [interior_Icc] at hs; rw [(hderiv s hs).deriv]; exact hLie s hs)
    (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  exact hab

/-! ## Trajectories stay inside the ball -/

/-- **Ball invariance.** Let `α₁(‖x‖) ≤ W₁(x) ≤ V(t, x)` and `V̇ ≤ 0` on the ball of radius `r`,
and pick a level `d` with `α₁⁻¹(d) < r`.  A trajectory that starts inside the ball with
`V(t₀, φ t₀) < d` stays inside the ball, on every interval `[t₀, t]`.

Were `φ` to reach the sphere `‖x‖ = r` first at `T_exit`, it would cross `‖x‖ = α₁⁻¹(d)` at
some earlier `T₁` while still inside the ball.  There `V` has not increased, so
`V(T₁, φ T₁) < d`; but also `V(T₁, φ T₁) ≥ W₁(φ T₁) ≥ α₁(‖φ T₁‖) > d`. -/
private lemma NA_ball_invariant
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ} {W₁ : ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {r : ℝ} {b1 : ℝ} {α1 : ClassK r b1} {d : ℝ}
    (hd_Ico : d ∈ Set.Ico 0 b1) (h_invd_lt_r : α1.invFun d < r)
    (hW1_lb : ∀ x : ℝⁿ, ‖x‖ < r → α1.toFun ‖x‖ ≤ W₁ x)
    (hV_lb  : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r → W₁ x ≤ V t x)
    (hLie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
        fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ 0)
    {φ : ℝ → ℝⁿ} {t₀ t : ℝ} (hφ : IsTrajectoryNA φ f t₀)
    (ht₀ : 0 ≤ t₀) (_ : t₀ ≤ t)
    (h_φt₀_lt_r : ‖φ t₀‖ < r) (h_Vt₀_lt_d : V t₀ (φ t₀) < d) :
    ∀ s : ℝ, t₀ ≤ s → s ≤ t → ‖φ s‖ < r := by
  have h_norm_cont : ContinuousOn (fun s => ‖φ s‖) (Set.Ici t₀) :=
    continuous_norm.comp_continuousOn hφ.continuousOn
  by_contra h_neg
  push Not at h_neg
  obtain ⟨s_bad, hs_lo, hs_hi, hs_bad⟩ := h_neg
  set E := {s ∈ Set.Icc t₀ s_bad | r ≤ ‖φ s‖}
  have hE_ne  : E.Nonempty := ⟨s_bad, ⟨hs_lo, le_rfl⟩, hs_bad⟩
  have hE_bdd : BddBelow E := ⟨t₀, fun s hs => hs.1.1⟩
  have hnorm_Icc : ∀ {u : ℝ}, ContinuousOn (fun s => ‖φ s‖) (Set.Icc t₀ u) :=
    fun {_} => h_norm_cont.mono (fun s hs => Set.mem_Ici.mpr hs.1)
  have hE_cl  : IsClosed E :=
    isClosed_Icc.isClosed_le continuousOn_const hnorm_Icc
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
      hnorm_Icc ⟨le_of_lt h_φt₀_lt_r, le_of_lt h_gt⟩
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
      have hcont := h_norm_cont.continuousAt (Ici_mem_nhds hT_gt)
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
    V_NA_nonincreasing hV_diff hφ le_rfl hT₁_ico.1
      (fun s hs => hLie_nonpos s (ht₀.trans hs.1.le) (φ s)
                     (h_stay s ⟨hs.1.le, hs.2.le.trans hT₁_ico.2.le⟩))
  have h_W1_gt_d : d < W₁ (φ T₁) :=
    calc d = α1.toFun (α1.invFun d) := (α1.right_inv hd_Ico).symm
         _ < α1.toFun ‖φ T₁‖       := α1.strict_mono (α1.inv_maps_to hd_Ico)
                                        ⟨norm_nonneg _, hT₁_lt_r⟩ hT₁_gt
         _ ≤ W₁ (φ T₁)             := hW1_lb (φ T₁) hT₁_lt_r
  linarith [hV_lb T₁ (ht₀.trans hT₁_ico.1) (φ T₁) hT₁_lt_r.le, hV_T₁_dec]

/-! ## Setup shared by the two Lyapunov theorems -/

/-- The level and radius both Lyapunov proofs work at: a level `d > 0` below `b₁` and `b₂`
(the ranges of the class `K` bounds `α₁` on `W₁` and `α₂` on `W₂`), and the radius
`c = α₂⁻¹(d)`, which lies in `(0, r)` and satisfies `α₂(c) = d`. -/
private lemma exists_sandwich_level {r b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (α₂ : ClassK r b₂) :
    ∃ d : ℝ, 0 < d ∧ d < b₁ ∧ d < b₂ ∧
      0 < α₂.invFun d ∧ α₂.invFun d < r ∧ α₂.toFun (α₂.invFun d) = d := by
  set d := min (b₁ / 2) (b₂ / 2)
  have hd_pos : 0 < d := lt_min (half_pos hb₁) (half_pos α₂.hb)
  have hd_lt_b₁ : d < b₁ := (min_le_left ..).trans_lt (half_lt_self hb₁)
  have hd_lt_b₂ : d < b₂ := (min_le_right ..).trans_lt (half_lt_self α₂.hb)
  have hd_mem : d ∈ Set.Ico 0 b₂ := ⟨hd_pos.le, hd_lt_b₂⟩
  have hc_pos : 0 < α₂.invFun d :=
    calc 0 = α₂.invFun 0 := α₂.symm.map_zero.symm
         _ < α₂.invFun d := α₂.symm.strict_mono ⟨le_rfl, α₂.hb⟩ hd_mem hd_pos
  exact ⟨d, hd_pos, hd_lt_b₁, hd_lt_b₂, hc_pos, (α₂.inv_maps_to hd_mem).2, α₂.right_inv hd_mem⟩

/-- Starting within `c` of the origin, where `c < r` and `α₂(c) = d`, forces `V(t, x) < d`:
`V(t, x) ≤ W₂(x) ≤ α₂(‖x‖) < α₂(c) = d`. -/
private lemma V_lt_d_of_norm_lt_c {V : ℝ → ℝⁿ → ℝ} {W₂ : ℝⁿ → ℝ} {r b₂ : ℝ}
    {α₂ : ClassK r b₂}
    (hV_ub : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r → V t x ≤ W₂ x)
    (hW₂_ub : ∀ x : ℝⁿ, ‖x‖ < r → W₂ x ≤ α₂.toFun ‖x‖)
    {c d : ℝ} (hc_lt_r : c < r) (h_α₂_c : α₂.toFun c = d)
    {t : ℝ} (ht : 0 ≤ t) {x : ℝⁿ} (hx : ‖x‖ < c) :
    V t x < d := by
  have hx_lt_r : ‖x‖ < r := hx.trans hc_lt_r
  calc V t x
      ≤ W₂ x         := hV_ub t ht x hx_lt_r.le
    _ ≤ α₂.toFun ‖x‖ := hW₂_ub x hx_lt_r
    _ < α₂.toFun c   := α₂.strict_mono ⟨norm_nonneg _, hx_lt_r⟩
                          ⟨(norm_nonneg _).trans hx.le, hc_lt_r⟩ hx
    _ = d            := h_α₂_c

/-- A function vanishing at the origin and positive elsewhere on the closed `r`-ball is
nonnegative on that ball. -/
private lemma W_nonneg {W : ℝⁿ → ℝ} {r : ℝ} (hW_zero : W 0 = 0)
    (hW_pos : ∀ x ∈ closedBall (0 : ℝⁿ) r, x ≠ 0 → 0 < W x) {x : ℝⁿ} (hx : ‖x‖ ≤ r) :
    0 ≤ W x := by
  by_cases hx0 : x = 0
  · simp [hx0, hW_zero]
  · exact (hW_pos x (mem_closedBall_zero_iff.mpr hx) hx0).le

/-! ## Lyapunov's uniform stability theorem (non-autonomous) -/

/-- **Lyapunov's uniform stability theorem** for `ẋ = f(t, x)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.8, hypotheses (4.22) and
(4.23). -/
@[blueprint "thm:lyapunov-uniformly-stable-NA"
  (title := "Lyapunov's uniform stability theorem")
  (statement := /-- Let $r > 0$ and let $V : \mathbb{R} \times \mathbb{R}^{n} \to
    \mathbb{R}$ be differentiable.  Suppose there are $W_{1}, W_{2}$, continuous on
    $\overline{B}(0,r)$, vanishing at the origin and strictly positive elsewhere on it, with
    \begin{enumerate}
      \item $W_{1}(x) \le V(t,x) \le W_{2}(x)$ for all $t \ge 0$ and $\|x\| \le r$;
      \item $DV(t,x)\,[\,(1, f(t,x))\,] \le 0$ for all $t \ge 0$ and $\|x\| \le r$.
    \end{enumerate}
    Then the origin is uniformly stable (\cref{def:uniformlyStableNA}).

    The sandwich is what makes the conclusion uniform in $t_{0}$: $W_{1}$ and $W_{2}$ do not
    depend on $t$, so the $\delta(\varepsilon)$ extracted from them does not either.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.8, hypotheses (4.22)
    and (4.23).
  -/)
  (proof := /-- Bound $W_{1}$ below and $W_{2}$ above by class $\mathcal{K}$ functions
    $\alpha_{1}, \alpha_{2}$ (\cref{thm:lyapunov-class-K-bounds}).  Fix a level $d$ below both
    ranges and set $c = \alpha_{2}^{-1}(d)$, so that starting within $c$ of the origin forces
    $V(t_{0}, \varphi(t_{0})) < d$.  Since $V$ is nonincreasing along the trajectory it stays
    below $d$, and $\alpha_{1}(\|\varphi(t)\|) \le V \le d$ confines $\varphi$ to the ball
    of radius $r$ --- so the estimate never leaves the region where the hypotheses hold.
    Chaining the sandwich gives
    $\alpha_{1}(\|\varphi(t)\|) \le \alpha_{2}(\|\varphi(t_{0})\|)$, i.e.
    $\|\varphi(t)\| \le (\alpha_{1}^{-1} \circ \alpha_{2})(\|\varphi(t_{0})\|)$, a class
    $\mathcal{K}$ bound; conclude by
    \cref{lem:uniformlyStableNA-iff-classK}. -/)]
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
  -- Exhibit the class K bound `α₁⁻¹ ∘ α₂` on `[0, c)`: from the `c`-ball `V` starts below `d`,
  -- so the trajectory stays in the `r`-ball, where
  -- `α₁(‖φ t‖) ≤ V(t, φ t) ≤ V(t₀, φ t₀) ≤ α₂(‖φ t₀‖)`.
  -- ── Step 1: class K bounds sandwiching W₁ and W₂ ─────────────────────────
  obtain ⟨b1_lower, b1_upper, α1, α1_upper, hW1_bounds⟩ :=
      LyapunovClassKBounds hr hW₁_cont hW₁_zero hW₁_pos
  obtain ⟨b2_lower, b2_upper, α2_lower, α2, hW2_bounds⟩ :=
      LyapunovClassKBounds hr hW₂_cont hW₂_zero hW₂_pos
  -- ── Step 2: a level `d` below both ranges, and the radius `c = α₂⁻¹(d)` ─────
  obtain ⟨d, hd_pos, hd_lt_b1, -, hc_pos, hc_lt_r, h_α2_c⟩ := exists_sandwich_level α1.hb α2
  set c := α2.invFun d
  -- ── Step 3: the class K bound `α₁⁻¹ ∘ α₂` on `[0, c)` ───────────────────────
  let α2_res : ClassK c d :=
    ClassK.of_strictMono hc_pos hd_pos α2.toFun α2.map_zero h_α2_c
      (α2.continuous.mono (fun x hx => ⟨hx.1, hx.2.trans_lt hc_lt_r⟩))
      (α2.strict_mono.mono (fun x hx => ⟨hx.1, hx.2.trans_lt hc_lt_r⟩))
  let α1_inv_res := α1.symm.restrict hd_pos hd_lt_b1
  let α_comp : ClassK c (α1_inv_res.toFun d) :=
    ClassK.comp α1_inv_res α2_res
  -- ── Step 4: every trajectory from the `c`-ball obeys it ──────────────────────
  rw [uniformlyStableNA_iff_classK f 0]
  refine ⟨c, α1_inv_res.toFun d, α_comp, ?_⟩
  intro t₀ ht₀ φ hφ h_init t ht
  simp only [sub_zero] at h_init ⊢
  have h_φt₀_lt_r : ‖φ t₀‖ < r := h_init.trans hc_lt_r
  have h_Vt₀_lt_d : V t₀ (φ t₀) < d :=
    V_lt_d_of_norm_lt_c (fun t ht x hx => (hV_sandwich t ht x hx).2)
      (fun x hx => (hW2_bounds x hx).2) hc_lt_r h_α2_c ht₀ h_init
  -- The trajectory stays in the `r`-ball, so the sandwich applies all along it.
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
      _ ≤ V t₀ (φ t₀)       := V_NA_nonincreasing hV_diff hφ le_rfl ht
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


/-- **Lyapunov's uniform asymptotic stability theorem** for `ẋ = f(t, x)`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.9, hypothesis (4.24). Khalil's
two "moreover" clauses are not part of this conclusion:
- the explicit bound `‖x(t)‖ ≤ β(‖x(t₀)‖, t − t₀)` — available here via
  `uniformlyAsymptoticStableNA_iff_classKL`;
- the global case, when `D = ℝⁿ` and `W₁` is radially unbounded. -/
@[blueprint "thm:lyapunov-uniformly-asymptotic-stable-NA"
  (title := "Lyapunov's uniform asymptotic stability theorem")
  (statement := /-- In the setting of \cref{thm:lyapunov-uniformly-stable-NA}, strengthen the
    derivative hypothesis to
    \[
      DV(t,x)\,[\,(1, f(t,x))\,] \le -W_{3}(x)
      \qquad \forall\, t \ge 0,\ \|x\| \le r,
    \]
    for a third $W_{3}$ continuous on $\overline{B}(0,r)$, vanishing at the origin and strictly
    positive elsewhere on it.  Then the origin is uniformly asymptotically stable
    (\cref{def:uniformlyAsymptoticStableNA}).

    A strictly negative $\dot{V}$ alone would not do: $W_{3}$ must be bounded away from zero on
    each annulus, which is exactly what positive definiteness of a function of $x$ alone
    buys.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.9, hypothesis (4.24).
    Khalil's two ``moreover'' clauses are not part of this conclusion:
    \begin{itemize}
      \item the explicit bound $\|x(t)\| \le \beta(\|x(t_{0})\|, t - t_{0})$, available here
        via \cref{lem:uniformlyAsymptoticStableNA-iff-classKL};
      \item the global case, when $D = \mathbb{R}^{n}$ and $W_{1}$ is radially unbounded.
    \end{itemize}
  -/)
  (proof := /-- As in \cref{thm:lyapunov-uniformly-stable-NA}, take class $\mathcal{K}$ bounds
    $\alpha_{1}, \alpha_{2}, \alpha_{3}$ for $W_{1}, W_{2}, W_{3}$.  Then
    $\dot{V} \le -W_{3}(x) \le -\alpha_{3}(\|x\|) \le
    -\alpha_{3}(\alpha_{2}^{-1}(V))$, so $v(t) = V(t, \varphi(t))$ satisfies the scalar
    differential inequality $D^{+}v \le -\alpha(v)$ with
    $\alpha = \alpha_{3} \circ \alpha_{2}^{-1}$ of class $\mathcal{K}$.
    \cref{thm:classK-dini-bound} supplies a class $\mathcal{KL}$ function $\sigma$ with
    $v(t) \le \sigma(v(t_{0}), t - t_{0})$.  Unwinding the sandwich,
    \[
      \|\varphi(t)\| \le \alpha_{1}^{-1}\bigl(\sigma(\alpha_{2}(\|\varphi(t_{0})\|),\,
        t - t_{0})\bigr),
    \]
    and the right-hand side is class $\mathcal{KL}$ in its two arguments; conclude by
    \cref{lem:uniformlyAsymptoticStableNA-iff-classKL}. -/)]
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
  -- Along a trajectory `v(t) = V(t, φ t)` obeys `D⁺v ≤ -α₃(α₂⁻¹(v))`, so the comparison lemma
  -- bounds it by a class KL `σ(v(t₀), t - t₀)`; the sandwich turns this into the class KL
  -- bound `‖φ t‖ ≤ α₁⁻¹(σ(α₂(‖φ t₀‖), t - t₀))`.
  -- ── Step 1: class K bounds for W₁, W₂, W₃ ──────────────────────────────────
  obtain ⟨b1_lower, b1_upper, α1, α1_upper, hW1_bounds⟩ :=
      LyapunovClassKBounds hr hW₁_cont hW₁_zero hW₁_pos
  obtain ⟨b2_lower, b2_upper, α2_lower, α2, hW2_bounds⟩ :=
      LyapunovClassKBounds hr hW₂_cont hW₂_zero hW₂_pos
  obtain ⟨b3_lower, b3_upper, α3, α3_upper, hW3_bounds⟩ :=
      LyapunovClassKBounds hr hW₃_cont hW₃_zero hW₃_pos
  -- ── Step 2: `d` and `c = α₂⁻¹(d)` as in the uniform-stability proof ────────
  obtain ⟨d, hd_pos, hd_lt_b1, hd_lt_b2, hc_pos, hc_lt_r, h_α2_c⟩ :=
    exists_sandwich_level α1.hb α2
  set c := α2.invFun d
  -- `V̇ ≤ -W₃ ≤ 0`, so the ball invariance of the uniform-stability proof applies.
  have hLie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
      fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ 0 := fun t ht x hx => by
    linarith [hLie_bound t ht x hx, W_nonneg hW₃_zero hW₃_pos hx]
  -- From the `c`-ball, `V` starts in `[0, d)` ...
  have hV_start : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝⁿ, ‖x‖ < c → V t₀ x ∈ Set.Ico 0 d :=
    fun t₀ ht₀ x hx =>
      ⟨(W_nonneg hW₁_zero hW₁_pos (hx.trans hc_lt_r).le).trans
          (hV_sandwich t₀ ht₀ x (hx.trans hc_lt_r).le).1,
        V_lt_d_of_norm_lt_c (fun t ht x hx => (hV_sandwich t ht x hx).2)
          (fun x hx => (hW2_bounds x hx).2) hc_lt_r h_α2_c ht₀ hx⟩
  -- ... and the trajectory never leaves the `r`-ball.
  have h_in_ball : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ → ‖φ t₀‖ < c →
      ∀ s : ℝ, t₀ ≤ s → ‖φ s‖ < r := fun t₀ ht₀ φ hφ h_init s hs =>
    NA_ball_invariant hV_diff ⟨hd_pos.le, hd_lt_b1⟩ (α1.inv_maps_to ⟨hd_pos.le, hd_lt_b1⟩).2
      (fun x hx => (hW1_bounds x hx).1) (fun t ht x hx => (hV_sandwich t ht x hx).1)
      hLie_nonpos hφ ht₀ hs (h_init.trans hc_lt_r) (hV_start t₀ ht₀ (φ t₀) h_init).2
      s hs le_rfl
  -- ── Step 3: the comparison function `α₃ ∘ α₂⁻¹` and its class KL bound `σ` ─
  -- Along trajectories `V̇ ≤ -W₃(x) ≤ -α₃(‖x‖) ≤ -α₃(α₂⁻¹(V))`.
  have h_α_comp : ∃ α_comp : ClassK d (α3.toFun c), ∀ y ∈ Set.Ico 0 d,
      α_comp.toFun y = α3.toFun (α2.invFun y) := by
    -- Compose `α₂⁻¹ : [0, d) → [0, c)` with `α₃` restricted to `[0, c)`.  As `c` is by
    -- definition `α₂⁻¹(d)`, the two domains match definitionally, so `ClassK.comp` needs no
    -- cast and the composite agrees with `α₃ ∘ α₂⁻¹` by `rfl`.
    let α2_inv_res := α2.symm.restrict hd_pos hd_lt_b2
    let α3_res : ClassK (α2.symm.toFun d) (α3.toFun c) := α3.restrict hc_pos hc_lt_r
    exact ⟨ClassK.comp α3_res α2_inv_res, fun _ _ => rfl⟩
  obtain ⟨α_comp, h_α_comp_eq⟩ := h_α_comp
  obtain ⟨σ, hσ_zero, hσ_general⟩ := classK_dini_bound α_comp
  -- ── Step 4: along trajectories, `V(t, φ t) ≤ σ(V(t₀, φ t₀), t − t₀)` ────────
  have hσ_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f t₀ → ‖φ t₀‖ < c → ∀ t : ℝ, t₀ ≤ t →
      V t (φ t) ≤ σ.toFun (V t₀ (φ t₀)) (t - t₀) := by
    intro t₀ ht₀ φ hφ h_init t ht
    have h_φs_lt_r : ∀ s : ℝ, t₀ ≤ s → ‖φ s‖ < r := h_in_ball t₀ ht₀ φ hφ h_init
    have hV_Ico_t₀ : V t₀ (φ t₀) ∈ Set.Ico 0 d := hV_start t₀ ht₀ (φ t₀) h_init
    -- V stays in [0, d) along the trajectory (needed by classK_dini_bound)
    have hv_range : ∀ s ∈ Set.Ico t₀ t, V s (φ s) ∈ Set.Ico 0 d := fun s hs => by
      have h_φs_r := h_φs_lt_r s hs.1
      have hV_nonneg : 0 ≤ V s (φ s) := (W_nonneg hW₁_zero hW₁_pos h_φs_r.le).trans
        (hV_sandwich s (ht₀.trans hs.1) (φ s) h_φs_r.le).1
      have hV_lt_d : V s (φ s) < d :=
        (V_NA_nonincreasing hV_diff hφ le_rfl hs.1
          (fun t' ht' => hLie_nonpos t' (ht₀.trans ht'.1.le) (φ t')
            (h_φs_lt_r t' ht'.1.le).le)).trans_lt hV_Ico_t₀.2
      exact ⟨hV_nonneg, hV_lt_d⟩
    -- The comparison hypothesis: D⁺(V(·, φ(·)))(s) ≤ −α_comp(V(s, φ(s))), by the chain
    -- V̇ ≤ −W₃(φ s) ≤ −α₃(‖φ s‖) ≤ −α₃(α₂⁻¹(V(s, φ(s)))) = −α_comp(V(s, φ(s))).
    have hDv : ∀ s ∈ Set.Ico t₀ t,
        D⁺ (fun s => V s (φ s)) s ≤ -α_comp.toFun (V s (φ s)) := by
      intro s hs
      rw [diniDerivRight_of_hasDerivWithinAt
            (hasDerivWithinAt_V_comp_traj_NA hV_diff hφ hs.1)]
      have h_φs_r   := h_φs_lt_r s hs.1
      have h_Lie    := hLie_bound s (ht₀.trans hs.1) (φ s) h_φs_r.le
      have hW3_lb   : α3.toFun ‖φ s‖ ≤ W₃ (φ s) := (hW3_bounds (φ s) h_φs_r).1
      have hV_le_α2 : V s (φ s) ≤ α2.toFun ‖φ s‖ :=
        (hV_sandwich s (ht₀.trans hs.1) (φ s) h_φs_r.le).2.trans (hW2_bounds (φ s) h_φs_r).2
      have hV_Ico   : V s (φ s) ∈ Set.Ico 0 d := hv_range s hs
      have hV_in_b2 : V s (φ s) ∈ Set.Ico 0 b2_upper := ⟨hV_Ico.1, hV_Ico.2.trans hd_lt_b2⟩
      calc fderiv ℝ (Function.uncurry V) (s, φ s) (1, f s (φ s))
          ≤ -W₃ (φ s)                 := h_Lie
        _ ≤ -α3.toFun ‖φ s‖           := neg_le_neg hW3_lb
        _ ≤ -α_comp.toFun (V s (φ s)) := neg_le_neg (by
              rw [h_α_comp_eq (V s (φ s)) hV_Ico]
              exact α3.strict_mono.monotoneOn (α2.inv_maps_to hV_in_b2)
                ⟨norm_nonneg _, h_φs_r⟩
                (calc α2.symm.toFun (V s (φ s))
                    ≤ α2.symm.toFun (α2.toFun ‖φ s‖) :=
                        α2.symm.strict_mono.monotoneOn hV_in_b2
                          (α2.maps_to ⟨norm_nonneg _, h_φs_r⟩) hV_le_α2
                  _ = ‖φ s‖ := α2.left_inv ⟨norm_nonneg _, h_φs_r⟩))
    -- Difference quotients are bounded (from HasDerivAt)
    have hv_bdd : ∀ s ∈ Set.Ico t₀ t,
        IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (V (s + h) (φ (s + h)) - V s (φ s)) / h) := by
      intro s hs
      have h_deriv := hasDerivWithinAt_V_comp_traj_NA hV_diff hφ hs.1
      exact h_deriv.tendsto_forward_slope.isBoundedUnder_le
    -- Apply the comparison lemma.
    have hv_cont : ContinuousOn (fun s => V s (φ s)) (Set.Icc t₀ t) :=
      hV_diff.continuous.comp_continuousOn
        (continuousOn_id.prodMk
          (hφ.continuousOn.mono (fun s hs => Set.mem_Ici.mpr hs.1)))
    exact hσ_general ht (fun s => V s (φ s)) hv_cont hV_Ico_t₀ hv_range hDv hv_bdd
  -- ── Step 5: the class KL bound β(r, s) = α₁⁻¹(σ(α₂(r), s)) ─────────────────
  -- `ClassKL.comp_left` takes a `ClassKInfty`, so the composition is assembled by hand from
  -- `comp_right` and `comp_left_K` rather than in one step.
  have h_beta : ∃ β : ClassKL c, ∀ r ∈ Set.Ico 0 c, ∀ s ≥ 0,
      α1.symm.toFun (σ.toFun (α2.toFun r) s) ≤ β.toFun r s := by
    set inner := σ.comp_right (α2.restrictTo hc_pos hc_lt_r h_α2_c)
    have h_inner_eq : ∀ r_val s, inner.toFun r_val s = σ.toFun (α2.toFun r_val) s := by
      intro r_val s
      -- `restrictTo` casts along `α₂(c) = d`; generalizing `d` lets `cases` remove the cast.
      have h_cast : ∀ {e} (h : α2.toFun c = e),
          (α2.restrictTo hc_pos hc_lt_r h).toFun r_val = α2.toFun r_val := by
        intro e h
        cases h
        rfl
      exact congrArg (fun x => σ.toFun x s) (h_cast h_α2_c)
    have h_range : ∀ r_val ∈ Set.Ico 0 c, ∀ s ≥ 0, inner.toFun r_val s < b1_lower := by
      intro r_val hr_val s hs
      -- `α₂` maps `[0, c)` into `[0, α₂(c)) = [0, d)`.
      have hα2r : α2.toFun r_val ∈ Set.Ico 0 d := by
        have hr_in : r_val ∈ Set.Ico 0 r := ⟨hr_val.1, hr_val.2.trans hc_lt_r⟩
        have hc_in : c ∈ Set.Ico 0 r := ⟨hc_pos.le, hc_lt_r⟩
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
  -- ── Step 6: every trajectory from the `c`-ball obeys β ─────────────────────
  rw [uniformlyAsymptoticStableNA_iff_classKL f 0]
  use c, β
  intro t₀ ht₀ φ hφ h_init t ht
  simp only [sub_zero] at h_init ⊢
  have h_φt₀_lt_r : ‖φ t₀‖ < r := h_init.trans hc_lt_r
  have h_φt_lt_r : ‖φ t‖ < r := h_in_ball t₀ ht₀ φ hφ h_init t ht
  have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hV_t0_Ico : V t₀ (φ t₀) ∈ Set.Ico 0 d := hV_start t₀ ht₀ (φ t₀) h_init
  have h_α2_t0_Ico : α2.toFun ‖φ t₀‖ ∈ Set.Ico 0 d :=
    ⟨(α2.maps_to ⟨norm_nonneg _, h_φt₀_lt_r⟩).1,
     (α2.strict_mono ⟨norm_nonneg _, h_φt₀_lt_r⟩ ⟨hc_pos.le, hc_lt_r⟩ h_init).trans_eq h_α2_c⟩
  have h_V_le_α2 : V t₀ (φ t₀) ≤ α2.toFun ‖φ t₀‖ :=
    (hV_sandwich t₀ ht₀ (φ t₀) h_φt₀_lt_r.le).2.trans (hW2_bounds (φ t₀) h_φt₀_lt_r).2
  -- `α₁(‖φ t‖) ≤ W₁ ≤ V ≤ σ(V(t₀, φ t₀), t - t₀) ≤ σ(α₂(‖φ t₀‖), t - t₀)`
  have h_chain : α1.toFun ‖φ t‖ ≤ σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) :=
    calc α1.toFun ‖φ t‖
      _ ≤ W₁ (φ t) := (hW1_bounds (φ t) h_φt_lt_r).1
      _ ≤ V t (φ t) := (hV_sandwich t (ht₀.trans ht) (φ t) h_φt_lt_r.le).1
      _ ≤ σ.toFun (V t₀ (φ t₀)) (t - t₀) := hσ_bound t₀ ht₀ φ hφ h_init t ht
      _ ≤ σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) :=
            (σ.strict_mono_r (t - t₀) ht_sub).monotoneOn hV_t0_Ico h_α2_t0_Ico h_V_le_α2
  -- Invert `α₁`, then bound by `β`.
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
  have h_norm_bound := h_inv_bound.trans h_beta_eval
  rwa [α1.left_inv ⟨norm_nonneg _, h_φt_lt_r⟩] at h_norm_bound
