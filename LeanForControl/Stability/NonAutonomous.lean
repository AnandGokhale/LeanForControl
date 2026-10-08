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

To leave the ball, `φ` would first have to reach a sphere `‖x‖ = ρ` with `α₁⁻¹(d) < ρ < r`.
Up to that time it is inside the ball, so `V` has not increased and is still below `d`; but on
that sphere `V ≥ W₁ ≥ α₁(ρ) > d`. -/
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
  /- Suppose `‖φ s‖ ≥ r`.  Pick `ρ` with `α₁⁻¹(d) < ρ < r` and let `τ ≤ s` be the first time
     `φ` reaches the `ρ`-sphere.  On `[t₀, τ]` the trajectory is inside the `r`-ball, so
     `V(τ, φ τ) ≤ V(t₀, φ t₀) < d`; yet `V(τ, φ τ) ≥ α₁(ρ) > d`. -/
  intro s hs₀ _
  by_contra h_out
  push Not at h_out
  -- Step 1. An intermediate radius `ρ`, strictly between `α₁⁻¹(d)` and `r`.
  obtain ⟨ρ, hρ_gt, hρ_lt⟩ := exists_between h_invd_lt_r
  have hd_inv_mem : α1.invFun d ∈ Set.Ico 0 r := α1.inv_maps_to hd_Ico
  -- Step 2. The trajectory starts inside the `ρ`-ball: `α₁(‖φ t₀‖) ≤ W₁ ≤ V < d`.
  have h_α1_start : α1.toFun ‖φ t₀‖ < α1.toFun (α1.invFun d) := by
    rw [α1.right_inv hd_Ico]
    exact (hW1_lb _ h_φt₀_lt_r).trans_lt
      ((hV_lb t₀ ht₀ _ h_φt₀_lt_r.le).trans_lt h_Vt₀_lt_d)
  have h_start : ‖φ t₀‖ < ρ :=
    ((α1.strict_mono_iff ⟨norm_nonneg _, h_φt₀_lt_r⟩ hd_inv_mem).mp h_α1_start).trans hρ_gt
  -- Step 3. The first time `τ ∈ [t₀, s]` at which `φ` reaches the `ρ`-sphere.
  obtain ⟨τ, hτ, hτ_norm, h_before⟩ := exists_first_sphere_hit (x_eq := (0 : ℝⁿ))
    (hφ.continuousOn.mono fun u hu => Set.mem_Ici.mpr hu.1) (by simpa using h_start)
    ⟨hs₀, le_rfl⟩ (by simpa using hρ_lt.le.trans h_out)
  simp only [sub_zero] at hτ_norm h_before
  have hτ_lt_r : ‖φ τ‖ < r := hτ_norm ▸ hρ_lt
  -- Step 4. On `[t₀, τ]` the trajectory is inside the `r`-ball, so `V` has not increased.
  have hV_τ_lt_d : V τ (φ τ) < d :=
    (V_NA_nonincreasing hV_diff hφ le_rfl hτ.1 fun u hu =>
      hLie_nonpos u (ht₀.trans hu.1.le) (φ u)
        ((h_before u ⟨hu.1.le, hu.2.le⟩).trans hρ_lt.le)).trans_lt h_Vt₀_lt_d
  -- Step 5. But on the `ρ`-sphere `V ≥ W₁ ≥ α₁(ρ) > α₁(α₁⁻¹(d)) = d`.
  have hV_τ_gt_d : d < V τ (φ τ) :=
    calc d = α1.toFun (α1.invFun d) := (α1.right_inv hd_Ico).symm
      _ < α1.toFun ‖φ τ‖ :=
          α1.strict_mono hd_inv_mem ⟨norm_nonneg _, hτ_lt_r⟩ (hτ_norm ▸ hρ_gt)
      _ ≤ W₁ (φ τ) := hW1_lb _ hτ_lt_r
      _ ≤ V τ (φ τ) := hV_lb τ (ht₀.trans hτ.1) _ hτ_lt_r.le
  exact absurd hV_τ_lt_d hV_τ_gt_d.not_gt

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

/-! ## Helpers for the uniform asymptotic stability theorem -/

/-- `ClassK.restrictTo` does not change the function: the cast along `α(c) = e` only retypes
the bound on the range. -/
private lemma restrictTo_toFun {a b : ℝ} (α : ClassK a b) {c e : ℝ} (hc_pos : 0 < c)
    (hc_lt : c < a) (h_eq : α.toFun c = e) (x : ℝ) :
    (α.restrictTo hc_pos hc_lt h_eq).toFun x = α.toFun x := by
  -- `e` is a variable, so `cases` can substitute it away and remove the cast.
  cases h_eq
  rfl

/-- A class `K` function maps `[0, c)` into `[0, α(c))`, written here with `α(c) = d`. -/
private lemma classK_mem_Ico_of_mem {a b c d : ℝ} (α : ClassK a b) (hc_lt : c < a)
    (h_eq : α.toFun c = d) {ρ : ℝ} (hρ : ρ ∈ Set.Ico 0 c) :
    α.toFun ρ ∈ Set.Ico 0 d := by
  have hρ_in : ρ ∈ Set.Ico 0 a := ⟨hρ.1, hρ.2.trans hc_lt⟩
  have hc_in : c ∈ Set.Ico 0 a := ⟨hρ.1.trans hρ.2.le, hc_lt⟩
  exact ⟨(α.maps_to hρ_in).1, h_eq ▸ α.strict_mono hρ_in hc_in hρ.2⟩

/-- If `σ(y, 0) ≤ y`, a class `KL` function maps `[0, d)` into itself at every time `s ≥ 0`:
by decay in `s`, `0 ≤ σ(y, s) ≤ σ(y, 0) ≤ y < d`. -/
private lemma classKL_mem_Ico {d : ℝ} {σ : ClassKL d}
    (hσ_zero : ∀ y ∈ Set.Ico 0 d, σ.toFun y 0 ≤ y) {y s : ℝ} (hy : y ∈ Set.Ico 0 d)
    (hs : 0 ≤ s) :
    σ.toFun y s ∈ Set.Ico 0 d := by
  have h_decay : σ.toFun y s ≤ σ.toFun y 0 :=
    σ.anti_s y hy (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  exact ⟨σ.nonneg y hy s hs, (h_decay.trans (hσ_zero y hy)).trans_lt hy.2⟩

/-- The pointwise comparison step: if `v ≤ α₂(ρ)` then `α₃(α₂⁻¹(v)) ≤ α₃(ρ)`, since both
`α₂⁻¹` and `α₃` are increasing. -/
private lemma classK_comp_invFun_le {r b₂ b₃ : ℝ} (α₂ : ClassK r b₂) (α₃ : ClassK r b₃)
    {ρ v : ℝ} (hρ : ρ ∈ Set.Ico 0 r) (hv : v ∈ Set.Ico 0 b₂) (hv_le : v ≤ α₂.toFun ρ) :
    α₃.toFun (α₂.invFun v) ≤ α₃.toFun ρ := by
  have h_inv_le : α₂.invFun v ≤ ρ :=
    calc α₂.invFun v
        ≤ α₂.invFun (α₂.toFun ρ) := (α₂.inv_mono_iff hv (α₂.maps_to hρ)).mpr hv_le
      _ = ρ                      := α₂.left_inv hρ
  exact α₃.strict_mono.monotoneOn (α₂.inv_maps_to hv) hρ h_inv_le

/-- **The comparison lemma along a trajectory.**  Let `σ` be the class `KL` bound that
`classK_dini_bound` attaches to a class `K` function `α`.  If `v(s) = V(s, φ s)` stays in
`[0, d)` on `[t₀, t]` and `V̇ ≤ -α(V)` there, then `V(t, φ t) ≤ σ(V(t₀, φ t₀), t - t₀)`.

This only checks the side conditions of `classK_dini_bound`: `v` is continuous, its Dini
derivative is the chain-rule derivative, and its difference quotients are bounded. -/
private lemma V_comp_traj_le_classKL
    {f : ℝ → ℝⁿ → ℝⁿ} {V : ℝ → ℝⁿ → ℝ}
    (hV_diff : Differentiable ℝ (Function.uncurry V))
    {d e : ℝ} {α : ClassK d e} {σ : ClassKL d}
    (hσ : ∀ {t₀ t : ℝ}, t₀ ≤ t → ∀ (v : ℝ → ℝ), ContinuousOn v (Set.Icc t₀ t) →
        v t₀ ∈ Set.Ico 0 d →
        (∀ s ∈ Set.Ico t₀ t, v s ∈ Set.Ico 0 d) →
        (∀ s ∈ Set.Ico t₀ t, D⁺ v s ≤ -α.toFun (v s)) →
        (∀ s ∈ Set.Ico t₀ t,
            IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (s + h) - v s) / h)) →
        v t ≤ σ.toFun (v t₀) (t - t₀))
    {φ : ℝ → ℝⁿ} {t₀ t : ℝ} (hφ : IsTrajectoryNA φ f t₀) (ht : t₀ ≤ t)
    (hv₀ : V t₀ (φ t₀) ∈ Set.Ico 0 d)
    (hv_range : ∀ s ∈ Set.Ico t₀ t, V s (φ s) ∈ Set.Ico 0 d)
    (hLie : ∀ s ∈ Set.Ico t₀ t,
        fderiv ℝ (Function.uncurry V) (s, φ s) (1, f s (φ s)) ≤ -α.toFun (V s (φ s))) :
    V t (φ t) ≤ σ.toFun (V t₀ (φ t₀)) (t - t₀) := by
  -- `v` is continuous, as a composition of continuous maps.
  have hv_cont : ContinuousOn (fun s => V s (φ s)) (Set.Icc t₀ t) :=
    hV_diff.continuous.comp_continuousOn
      (continuousOn_id.prodMk (hφ.continuousOn.mono (fun s hs => Set.mem_Ici.mpr hs.1)))
  -- Its right Dini derivative is the chain-rule derivative, hence `≤ -α(v)`.
  have hDv : ∀ s ∈ Set.Ico t₀ t, D⁺ (fun s => V s (φ s)) s ≤ -α.toFun (V s (φ s)) :=
    fun s hs => by
      rw [diniDerivRight_of_hasDerivWithinAt (hasDerivWithinAt_V_comp_traj_NA hV_diff hφ hs.1)]
      exact hLie s hs
  -- Its forward difference quotients converge, so they are bounded.
  have hv_bdd : ∀ s ∈ Set.Ico t₀ t, IsBoundedUnder (· ≤ ·) (𝓝[>] 0)
      (fun h => (V (s + h) (φ (s + h)) - V s (φ s)) / h) := fun s hs =>
    (hasDerivWithinAt_V_comp_traj_NA hV_diff hφ hs.1).tendsto_forward_slope.isBoundedUnder_le
  exact hσ ht (fun s => V s (φ s)) hv_cont hv₀ hv_range hDv hv_bdd

/-- **The class `KL` bound of the asymptotic theorem.**  Given `σ : ClassKL d` with
`σ(y, 0) ≤ y`, a class `K` function `α₁` whose range `[0, b₁)` contains `[0, d)`, and a class
`K` function `α₂` with `α₂(c) = d`, the composite `β(ρ, s) = α₁⁻¹(σ(α₂(ρ), s))` is class `KL`
on `[0, c)`. -/
private lemma exists_classKL_comp_sandwich {r b₁ b₂ c d : ℝ}
    (α₁ : ClassK r b₁) (α₂ : ClassK r b₂) {σ : ClassKL d}
    (hσ_zero : ∀ y ∈ Set.Ico 0 d, σ.toFun y 0 ≤ y)
    (hc_pos : 0 < c) (hc_lt_r : c < r) (h_α₂_c : α₂.toFun c = d) (hd_lt_b₁ : d < b₁) :
    ∃ β : ClassKL c, ∀ ρ s, β.toFun ρ s = α₁.invFun (σ.toFun (α₂.toFun ρ) s) := by
  /- `ClassKL.comp_left` takes a `ClassKInfty`, so `β` is assembled in two steps: first
     `σ ∘ α₂` by `comp_right`, then `α₁⁻¹ ∘ (σ ∘ α₂)` by `comp_left_K`. -/
  -- Step 1. The inner composite `σ(α₂(ρ), s)`, with `α₂` restricted to `[0, c) → [0, d)`.
  set inner := σ.comp_right (α₂.restrictTo hc_pos hc_lt_r h_α₂_c)
  have h_inner_eq : ∀ ρ s, inner.toFun ρ s = σ.toFun (α₂.toFun ρ) s := fun ρ s =>
    congrArg (fun y => σ.toFun y s) (restrictTo_toFun α₂ hc_pos hc_lt_r h_α₂_c ρ)
  -- Step 2. Its values stay below `d < b₁`, inside the domain of `α₁⁻¹`.
  have h_range : ∀ ρ ∈ Set.Ico 0 c, ∀ s ≥ 0, inner.toFun ρ s < b₁ := fun ρ hρ s hs => by
    rw [h_inner_eq]
    exact (classKL_mem_Ico hσ_zero (classK_mem_Ico_of_mem α₂ hc_lt_r h_α₂_c hρ) hs).2.trans
      hd_lt_b₁
  -- Step 3. Post-compose with `α₁⁻¹`.
  exact ⟨inner.comp_left_K α₁.symm h_range, fun ρ s => congrArg α₁.invFun (h_inner_eq ρ s)⟩
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
  /- Along a trajectory `v(t) = V(t, φ t)` obeys `D⁺v ≤ -α₃(α₂⁻¹(v))`, so the comparison lemma
     bounds it by a class KL `σ(v(t₀), t - t₀)`; the sandwich turns this into the class KL
     bound `‖φ t‖ ≤ α₁⁻¹(σ(α₂(‖φ t₀‖), t - t₀))`. -/
  -- Step 1. Class K bounds for `W₁`, `W₂`, `W₃`.
  obtain ⟨b1_lower, b1_upper, α1, α1_upper, hW1_bounds⟩ :=
      LyapunovClassKBounds hr hW₁_cont hW₁_zero hW₁_pos
  obtain ⟨b2_lower, b2_upper, α2_lower, α2, hW2_bounds⟩ :=
      LyapunovClassKBounds hr hW₂_cont hW₂_zero hW₂_pos
  obtain ⟨b3_lower, b3_upper, α3, α3_upper, hW3_bounds⟩ :=
      LyapunovClassKBounds hr hW₃_cont hW₃_zero hW₃_pos
  -- `V̇ ≤ -W₃ ≤ 0`, so the ball invariance of the uniform-stability proof applies.
  have hLie_nonpos : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r →
      fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ 0 := fun t ht x hx => by
    linarith [hLie_bound t ht x hx, W_nonneg hW₃_zero hW₃_pos hx]
  -- `0 ≤ W₁ ≤ V` on the `r`-ball.
  have hV_nonneg : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ ≤ r → 0 ≤ V t x := fun t ht x hx =>
    (W_nonneg hW₁_zero hW₁_pos hx).trans (hV_sandwich t ht x hx).1
  -- `V ≤ W₂ ≤ α₂(‖x‖)` on the open `r`-ball.
  have hV_le_α2 : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ < r → V t x ≤ α2.toFun ‖x‖ :=
    fun t ht x hx => (hV_sandwich t ht x hx.le).2.trans (hW2_bounds x hx).2
  -- Step 2. The level `d` and radius `c = α₂⁻¹(d)` of the uniform-stability proof.
  obtain ⟨d, hd_pos, hd_lt_b1, hd_lt_b2, hc_pos, hc_lt_r, h_α2_c⟩ :=
    exists_sandwich_level α1.hb α2
  set c := α2.invFun d
  -- Step 3. A trajectory from the `c`-ball never leaves the `r`-ball ...
  have h_in_ball : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ → ‖φ t₀‖ < c →
      ∀ s : ℝ, t₀ ≤ s → ‖φ s‖ < r := fun t₀ ht₀ φ hφ h_init s hs =>
    NA_ball_invariant hV_diff ⟨hd_pos.le, hd_lt_b1⟩ (α1.inv_maps_to ⟨hd_pos.le, hd_lt_b1⟩).2
      (fun x hx => (hW1_bounds x hx).1) (fun t ht x hx => (hV_sandwich t ht x hx).1)
      hLie_nonpos hφ ht₀ hs (h_init.trans hc_lt_r)
      (V_lt_d_of_norm_lt_c (fun t ht x hx => (hV_sandwich t ht x hx).2)
        (fun x hx => (hW2_bounds x hx).2) hc_lt_r h_α2_c ht₀ h_init)
      s hs le_rfl
  -- ... and keeps `V` in `[0, d)`: it starts below `d` and is nonincreasing.
  have hV_range : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ → ‖φ t₀‖ < c →
      ∀ s : ℝ, t₀ ≤ s → V s (φ s) ∈ Set.Ico 0 d := fun t₀ ht₀ φ hφ h_init s hs => by
    have hV_t₀_lt_d : V t₀ (φ t₀) < d :=
      V_lt_d_of_norm_lt_c (fun t ht x hx => (hV_sandwich t ht x hx).2)
        (fun x hx => (hW2_bounds x hx).2) hc_lt_r h_α2_c ht₀ h_init
    have hV_dec : V s (φ s) ≤ V t₀ (φ t₀) :=
      V_NA_nonincreasing hV_diff hφ le_rfl hs fun u hu =>
        hLie_nonpos u (ht₀.trans hu.1.le) (φ u) (h_in_ball t₀ ht₀ φ hφ h_init u hu.1.le).le
    exact ⟨hV_nonneg s (ht₀.trans hs) (φ s) (h_in_ball t₀ ht₀ φ hφ h_init s hs).le,
      hV_dec.trans_lt hV_t₀_lt_d⟩
  -- Step 4. The comparison function `α₃ ∘ α₂⁻¹` on `[0, d)` and its class KL bound `σ`.
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
  -- In the `r`-ball, `V̇ ≤ -W₃(x) ≤ -α₃(‖x‖) ≤ -α₃(α₂⁻¹(V))`.
  have hLie_comp : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝⁿ, ‖x‖ < r → V t x ∈ Set.Ico 0 d →
      fderiv ℝ (Function.uncurry V) (t, x) (1, f t x) ≤ -α_comp.toFun (V t x) :=
    fun t ht x hx hV => by
      have h_comp_le : α_comp.toFun (V t x) ≤ α3.toFun ‖x‖ := by
        rw [h_α_comp_eq _ hV]
        exact classK_comp_invFun_le α2 α3 ⟨norm_nonneg _, hx⟩ ⟨hV.1, hV.2.trans hd_lt_b2⟩
          (hV_le_α2 t ht x hx)
      calc fderiv ℝ (Function.uncurry V) (t, x) (1, f t x)
          ≤ -W₃ x                  := hLie_bound t ht x hx.le
        _ ≤ -α3.toFun ‖x‖          := neg_le_neg (hW3_bounds x hx).1
        _ ≤ -α_comp.toFun (V t x)  := neg_le_neg h_comp_le
  -- Step 5. Along trajectories from the `c`-ball, `V(t, φ t) ≤ σ(V(t₀, φ t₀), t − t₀)`.
  have hσ_bound : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f t₀ → ‖φ t₀‖ < c → ∀ t : ℝ, t₀ ≤ t →
      V t (φ t) ≤ σ.toFun (V t₀ (φ t₀)) (t - t₀) := fun t₀ ht₀ φ hφ h_init t ht =>
    V_comp_traj_le_classKL hV_diff hσ_general hφ ht (hV_range t₀ ht₀ φ hφ h_init t₀ le_rfl)
      (fun s hs => hV_range t₀ ht₀ φ hφ h_init s hs.1)
      (fun s hs => hLie_comp s (ht₀.trans hs.1) (φ s) (h_in_ball t₀ ht₀ φ hφ h_init s hs.1)
        (hV_range t₀ ht₀ φ hφ h_init s hs.1))
  -- Step 6. The class KL bound `β(ρ, s) = α₁⁻¹(σ(α₂(ρ), s))`.
  obtain ⟨β, hβ_eq⟩ := exists_classKL_comp_sandwich α1 α2 hσ_zero hc_pos hc_lt_r h_α2_c hd_lt_b1
  -- Step 7. Every trajectory from the `c`-ball obeys `β`.
  rw [uniformlyAsymptoticStableNA_iff_classKL f 0]
  refine ⟨c, β, ?_⟩
  intro t₀ ht₀ φ hφ h_init t ht
  simp only [sub_zero] at h_init ⊢
  have h_φt₀_lt_r : ‖φ t₀‖ < r := h_init.trans hc_lt_r
  have h_φt_lt_r : ‖φ t‖ < r := h_in_ball t₀ ht₀ φ hφ h_init t ht
  have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  -- `V(t₀, φ t₀)` and `α₂(‖φ t₀‖)` lie in `[0, d)`, and `σ(·, t - t₀)` keeps `[0, d)`.
  have hV_t₀_mem : V t₀ (φ t₀) ∈ Set.Ico 0 d := hV_range t₀ ht₀ φ hφ h_init t₀ le_rfl
  have h_α2_t₀_mem : α2.toFun ‖φ t₀‖ ∈ Set.Ico 0 d :=
    classK_mem_Ico_of_mem α2 hc_lt_r h_α2_c ⟨norm_nonneg _, h_init⟩
  have h_σ_mem : σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) ∈ Set.Ico 0 d :=
    classKL_mem_Ico hσ_zero h_α2_t₀_mem ht_sub
  -- `α₁(‖φ t‖) ≤ W₁ ≤ V ≤ σ(V(t₀, φ t₀), t - t₀) ≤ σ(α₂(‖φ t₀‖), t - t₀)`.
  have h_chain : α1.toFun ‖φ t‖ ≤ σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) :=
    calc α1.toFun ‖φ t‖
      _ ≤ W₁ (φ t) := (hW1_bounds (φ t) h_φt_lt_r).1
      _ ≤ V t (φ t) := (hV_sandwich t (ht₀.trans ht) (φ t) h_φt_lt_r.le).1
      _ ≤ σ.toFun (V t₀ (φ t₀)) (t - t₀) := hσ_bound t₀ ht₀ φ hφ h_init t ht
      _ ≤ σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) :=
            (σ.strict_mono_r (t - t₀) ht_sub).monotoneOn hV_t₀_mem h_α2_t₀_mem
              (hV_le_α2 t₀ ht₀ (φ t₀) h_φt₀_lt_r)
  -- Invert `α₁`, which is increasing on `[0, b₁) ⊇ [0, d)`.
  have h_α1_mem : α1.toFun ‖φ t‖ ∈ Set.Ico 0 b1_lower := α1.maps_to ⟨norm_nonneg _, h_φt_lt_r⟩
  have h_σ_mem_b1 : σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀) ∈ Set.Ico 0 b1_lower :=
    ⟨h_σ_mem.1, h_σ_mem.2.trans hd_lt_b1⟩
  calc ‖φ t‖
      = α1.invFun (α1.toFun ‖φ t‖) := (α1.left_inv ⟨norm_nonneg _, h_φt_lt_r⟩).symm
    _ ≤ α1.invFun (σ.toFun (α2.toFun ‖φ t₀‖) (t - t₀)) :=
        (α1.inv_mono_iff h_α1_mem h_σ_mem_b1).mpr h_chain
    _ = β.toFun ‖φ t₀‖ (t - t₀) := (hβ_eq _ _).symm
