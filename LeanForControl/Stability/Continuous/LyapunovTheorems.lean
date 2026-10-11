import LeanForControl.Stability.Continuous.LyapunovFunctions
import LeanForControl.Stability.LyapunovBounds
import LeanForControl.Stability.ClassKDecay
import LeanForControl.Analysis.Continuity
import LeanForControl.Analysis.DiniDeriv
import LeanForControl.Comparison.ClassKL
import Architect

/-!
# `Stability.Continuous.LyapunovTheorems` — what the Lyapunov certificates certify

Lyapunov's direct method for `ẋ = f(t, x)`: the certificates of
`Stability.Continuous.LyapunovFunctions` imply the stability notions of
`Stability.Continuous.Defs`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorems 4.8 and 4.9.

## Main results

* `IsUniformLyapunovFunction.uniformlyStable` — a uniform Lyapunov function certifies uniform
  stability (Khalil, Theorem 4.8).
* `IsStrictUniformLyapunovFunction.uniformlyAsymptoticallyStable` — a strict uniform Lyapunov
  function certifies uniform asymptotic stability (Khalil, Theorem 4.9).

## The two arguments

* **Trapping.**  `V` does not increase along a trajectory, and `W₁(x) ≤ V(t, x) ≤ W₂(x)` with
  `W₁, W₂` independent of `t`.  A trajectory starting where `W₂` is small therefore keeps `V`
  small, and so `W₁` small: it cannot reach a sphere on which `W₁` is large.  This gives uniform
  stability directly: to stay in the `ε`-ball, run the argument on a radius below `ε`.
* **Decay.**  With `V̇ ≤ -W₃`, the sandwich turns this into the scalar inequality
  `D⁺v ≤ -α(v)` for `v(t) = V(t, x(t))` and a class `K` function `α`.  The comparison lemma bounds
  `v` by a class `KL` function, and the sandwich turns that into a class `KL` bound on
  `‖x(t) - x_eq‖`, from which the uniform convergence time follows.

Only segment trajectories are used, so no solution is assumed to exist for all time.  The state
space is `ℝⁿ`, because the class `K` bounds on positive definite functions
(`LyapunovClassKBounds`) use compactness of its spheres.
-/

open Set Filter Topology Metric

namespace ContinuousSystem

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Uniform convergence from a class `KL` bound -/

/-- A class `KL` bound on the trajectories from the `a`-ball gives a uniform convergence time from
every smaller ball, of radius `c < a`: past the time at which `β(c, ·)` drops below `η`, so does
every deviation.  The radius `a` itself is out of reach in general, since `β(ρ, ·)` need not decay
uniformly as `ρ → a`. -/
@[blueprint "lem:continuousSystem-hasUniformConvergenceTime-of-classKL"
  (title := "Uniform convergence from a class $\\mathcal{KL}$ bound")
  (latexEnv := "lemma")
  (statement := /-- Let $\beta$ be class $\mathcal{KL}$ on $[0, a) \times [0, \infty)$
    (\cref{def:isClassKL}), and suppose every trajectory on a segment $[t_0, t_1]$, $t_0 \ge 0$,
    with $\|x(t_0) - x_{\mathrm{eq}}\| < a$ satisfies
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$ on the segment.
    Then for every $c < a$, trajectories from the ball of radius $c$ have a uniform convergence
    time (\cref{def:continuousSystem-hasUniformConvergenceTime}). -/)
  (proof := /-- For $c \le 0$ no trajectory starts in the ball.  Otherwise, given $\eta > 0$,
    pick $T$ with $\beta(c, s) < \eta$ for $s \ge T$.  For $t \ge t_0 + T$, monotonicity of
    $\beta$ in its first argument gives
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(c, t - t_0) < \eta$. -/)]
lemma hasUniformConvergenceTime_of_classKL {s : ContinuousSystem E Unit Y} {x_eq : E} {a c : ℝ}
    (β : ClassKL a) (hc : c < a)
    (hβ : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E), s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
      ‖x t₀ - x_eq‖ < a → ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀)) :
    s.HasUniformConvergenceTime x_eq c := by
  intro η hη
  rcases lt_or_ge c 0 with hc₀ | hc₀
  · -- No trajectory starts within a negative radius, so any time will do.
    exact ⟨1, one_pos, fun t₀ _ t₁ x _ h_init =>
      (lt_asymm hc₀ ((norm_nonneg _).trans_lt h_init)).elim⟩
  have hc_mem : c ∈ Ico 0 a := ⟨hc₀, hc⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (β.tendsto_zero c hc_mem (Iio_mem_nhds hη))
  -- `max T 0 + 1` only makes the convergence time positive.
  refine ⟨max T 0 + 1, by linarith [le_max_right T 0], fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
  have h_elapsed : T ≤ t - t₀ := by linarith [le_max_left T 0, ht.1]
  have h_elapsed_nonneg : 0 ≤ t - t₀ := by linarith [le_max_right T 0, ht.1]
  have h_init_mem : ‖x t₀ - x_eq‖ ∈ Ico 0 a := ⟨norm_nonneg _, h_init.trans hc⟩
  calc ‖x t - x_eq‖
      ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀) :=
        hβ t₀ ht₀ t₁ x hx h_init_mem.2 t ⟨by linarith, ht.2⟩
    _ ≤ β.toFun c (t - t₀) :=
        (β.strict_mono_r _ h_elapsed_nonneg h_init_mem hc_mem h_init).le
    _ < η := hT _ h_elapsed

section Euclidean

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## Comparison-function setup -/

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
  have hd_mem : d ∈ Ico 0 b₂ := ⟨hd_pos.le, hd_lt_b₂⟩
  have hc_pos : 0 < α₂.invFun d :=
    calc 0 = α₂.invFun 0 := α₂.symm.map_zero.symm
         _ < α₂.invFun d := α₂.symm.strict_mono ⟨le_rfl, α₂.hb⟩ hd_mem hd_pos
  exact ⟨d, hd_pos, hd_lt_b₁, hd_lt_b₂, hc_pos, (α₂.inv_maps_to hd_mem).2, α₂.right_inv hd_mem⟩

/-! ## Trapping -/

/-- **Trapping.**  Let `V` be a Lyapunov function on `D`, with `W₁(x) ≤ V(t, x)` on `D` and
`α₁(‖x - x_eq‖) ≤ W₁(x)` on a closed `r`-ball inside `D`, and pick a level `d` with
`α₁⁻¹(d) < r`.  A trajectory on `[t₀, t₁]` that starts inside the ball with
`V(t₀, x(t₀)) < d` stays inside the ball.

To leave the ball, `x` would first have to reach a sphere `‖x - x_eq‖ = ρ` with
`α₁⁻¹(d) < ρ < r`.  Up to that time it is inside the ball, so `V` has not increased and is still
below `d`; but on that sphere `V ≥ W₁ ≥ α₁(ρ) > d`. -/
private lemma norm_lt_of_trapped {s : ContinuousSystem ℝⁿ Unit Y} {V : ℝ → ℝⁿ → ℝ}
    {W₁ : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ} (hV : s.IsLyapunovFunction V x_eq D)
    (hV_lb : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ D, W₁ y ≤ V t y)
    {r b₁ : ℝ} (hrD : closedBall x_eq r ⊆ D) {α₁ : ClassK r b₁}
    (hW₁ : ∀ y : ℝⁿ, ‖y - x_eq‖ < r → α₁.toFun ‖y - x_eq‖ ≤ W₁ y) {d : ℝ} (hd : d ∈ Ico 0 b₁)
    {t₀ t₁ : ℝ} {x : ℝ → ℝⁿ} (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (ht₀ : 0 ≤ t₀) (h_start : ‖x t₀ - x_eq‖ < r) (hV_start : V t₀ (x t₀) < d) :
    ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < r := by
  have hD : ∀ y : ℝⁿ, ‖y - x_eq‖ ≤ r → y ∈ D := fun y hy => hrD (mem_closedBall_iff_norm.mpr hy)
  intro t ht
  by_contra h_out
  push Not at h_out
  -- Step 1. An intermediate radius `ρ`, strictly between `α₁⁻¹(d)` and `r`.
  have hd_inv_mem : α₁.invFun d ∈ Ico 0 r := α₁.inv_maps_to hd
  obtain ⟨ρ, hρ_gt, hρ_lt⟩ := exists_between hd_inv_mem.2
  -- Step 2. The trajectory starts inside the `ρ`-ball: `α₁(‖x t₀ - x_eq‖) ≤ W₁ ≤ V < d`.
  have h_α₁_start : α₁.toFun ‖x t₀ - x_eq‖ < α₁.toFun (α₁.invFun d) := by
    rw [α₁.right_inv hd]
    exact (hW₁ _ h_start).trans_lt ((hV_lb t₀ ht₀ _ (hD _ h_start.le)).trans_lt hV_start)
  have h_start_ρ : ‖x t₀ - x_eq‖ < ρ :=
    ((α₁.strict_mono_iff ⟨norm_nonneg _, h_start⟩ hd_inv_mem).mp h_α₁_start).trans hρ_gt
  -- Step 3. The first time `τ ∈ [t₀, t]` at which `x` reaches the `ρ`-sphere.
  obtain ⟨τ, hτ, hτ_norm, h_before⟩ := exists_first_sphere_hit
    ((IsIntegralCurveOn.continuousOn hx).mono (Icc_subset_Icc_right ht.2)) h_start_ρ
    ⟨ht.1, le_rfl⟩ (hρ_lt.le.trans h_out)
  have hτ_lt_r : ‖x τ - x_eq‖ < r := hτ_norm ▸ hρ_lt
  -- Step 4. On `[t₀, τ]` the trajectory is inside the `r`-ball, so `V` has not increased.
  have hV_τ_lt_d : V τ (x τ) < d := by
    have h_anti := IsTrajectoryOn.antitoneOn_of_lieDerivative_nonpos
      (IsIntegralCurveOn.mono hx (Icc_subset_Icc_right (hτ.2.trans ht.2))) hV.differentiable
      fun u hu =>
        hV.lie_nonpos u (ht₀.trans hu.1.le) (x u)
          (hD _ ((h_before u ⟨hu.1.le, hu.2.le⟩).trans hρ_lt.le))
    exact (h_anti ⟨le_rfl, hτ.1⟩ ⟨hτ.1, le_rfl⟩ hτ.1).trans_lt hV_start
  -- Step 5. But on the `ρ`-sphere `V ≥ W₁ ≥ α₁(ρ) > α₁(α₁⁻¹(d)) = d`.
  have hV_τ_gt_d : d < V τ (x τ) :=
    calc d = α₁.toFun (α₁.invFun d) := (α₁.right_inv hd).symm
      _ < α₁.toFun ‖x τ - x_eq‖ :=
          α₁.strict_mono hd_inv_mem ⟨norm_nonneg _, hτ_lt_r⟩ (hτ_norm ▸ hρ_gt)
      _ ≤ W₁ (x τ) := hW₁ _ hτ_lt_r
      _ ≤ V τ (x τ) := hV_lb τ (ht₀.trans hτ.1) _ (hD _ hτ_lt_r.le)
  exact lt_asymm hV_τ_lt_d hV_τ_gt_d

/-- The bound `V(t, y) < d = α₂(c)` from the `c`-ball: `V ≤ W₂ ≤ α₂(‖y - x_eq‖) < α₂(c)`. -/
private lemma lt_level_of_norm_lt {V : ℝ → ℝⁿ → ℝ} {W₂ : ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hV_ub : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ D, V t y ≤ W₂ y)
    {r b₂ : ℝ} (hrD : closedBall x_eq r ⊆ D) {α₂ : ClassK r b₂}
    (hW₂ : ∀ y : ℝⁿ, ‖y - x_eq‖ < r → W₂ y ≤ α₂.toFun ‖y - x_eq‖)
    {c d : ℝ} (hc_lt_r : c < r) (h_α₂_c : α₂.toFun c = d)
    {t : ℝ} (ht : 0 ≤ t) {y : ℝⁿ} (hy : ‖y - x_eq‖ < c) :
    V t y < d := by
  have hy_r : ‖y - x_eq‖ < r := hy.trans hc_lt_r
  calc V t y
      ≤ W₂ y                   := hV_ub t ht y (hrD (mem_closedBall_iff_norm.mpr hy_r.le))
    _ ≤ α₂.toFun ‖y - x_eq‖    := hW₂ y hy_r
    _ < α₂.toFun c             := α₂.strict_mono ⟨norm_nonneg _, hy_r⟩
                                    ⟨(norm_nonneg _).trans hy.le, hc_lt_r⟩ hy
    _ = d                      := h_α₂_c

/-! ## Lyapunov's uniform stability theorem -/

/-- **Lyapunov's uniform stability theorem**: a uniform Lyapunov function certifies uniform
stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.8. -/
@[blueprint "thm:continuousSystem-isUniformLyapunovFunction-uniformlyStable"
  (title := "Lyapunov's uniform stability theorem")
  (statement := /-- If $V$ is a uniform Lyapunov function for $x_{\mathrm{eq}}$
    (\cref{def:continuousSystem-isUniformLyapunovFunction}) on a system with state space
    $\mathbb{R}^n$, then $x_{\mathrm{eq}}$ is uniformly stable
    (\cref{def:continuousSystem-uniformlyStable}).

    The sandwich $W_1(x) \le V(t, x) \le W_2(x)$ is what makes the conclusion uniform in $t_0$:
    $W_1$ and $W_2$ do not depend on $t$, so neither does the $\delta(\varepsilon)$ extracted
    from them.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.8. -/)
  (proof := /-- Given $\varepsilon$, work on a radius $r \le \varepsilon$ whose closed ball lies
    in the region of the certificate.  Bound $W_1$ below and $W_2$ above by class $\mathcal{K}$
    functions $\alpha_1, \alpha_2$ on it (\cref{thm:lyapunov-class-K-bounds}), fix a level $d$
    below both ranges, and take $\delta = \alpha_2^{-1}(d)$: starting within $\delta$ of
    $x_{\mathrm{eq}}$ forces $V(t_0, x(t_0)) < d$.  To leave the $r$-ball the trajectory would
    first cross a sphere on which $W_1 > d$; up to that time $V$ has not increased
    (\cref{lem:continuousSystem-isTrajectoryOn-antitoneOn-of-lieDerivative-nonpos}), so it is
    still below $d$, a contradiction. -/)]
theorem IsUniformLyapunovFunction.uniformlyStable [NeZero n] {s : ContinuousSystem ℝⁿ Unit Y}
    {V : ℝ → ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ} (hV : s.IsUniformLyapunovFunction V x_eq D) :
    s.UniformlyStable x_eq := by
  obtain ⟨W₁, hW₁, hV_lb⟩ := hV.lower
  obtain ⟨W₂, hW₂, hV_ub⟩ := hV.upper
  obtain ⟨R, hR, hRD⟩ := nhds_basis_closedBall.mem_iff.mp hV.nhds
  intro ε hε
  -- Step 1. Work on a radius `r ≤ ε` whose closed ball lies in `D`.
  set r := min ε R
  have hr : 0 < r := lt_min hε hR
  have hrD : closedBall x_eq r ⊆ D := (closedBall_subset_closedBall (min_le_right ε R)).trans hRD
  -- Step 2. Class `K` bounds for `W₁` and `W₂`, a level `d`, and the radius `δ = α₂⁻¹(d)`.
  obtain ⟨b₁, _, α₁, _, hW₁_bd⟩ := LyapunovClassKBounds hr hrD hW₁
  obtain ⟨_, b₂, _, α₂, hW₂_bd⟩ := LyapunovClassKBounds hr hrD hW₂
  obtain ⟨d, hd_pos, hd_lt_b₁, -, hδ_pos, hδ_lt_r, h_α₂_δ⟩ := exists_sandwich_level α₁.hb α₂
  -- Step 3. Trajectories from the `δ`-ball are trapped in the `r`-ball, inside the `ε`-ball.
  refine ⟨α₂.invFun d, hδ_pos, fun t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
  have h_trapped := norm_lt_of_trapped hV.toIsLyapunovFunction hV_lb hrD
    (fun y hy => (hW₁_bd y hy).1) ⟨hd_pos.le, hd_lt_b₁⟩ hx ht₀ (h_init.trans hδ_lt_r)
    (lt_level_of_norm_lt hV_ub hrD (fun y hy => (hW₂_bd y hy).2) hδ_lt_r h_α₂_δ ht₀ h_init)
  exact (h_trapped t ht).trans_le (min_le_left ε R)

/-! ## The comparison lemma along a trajectory -/

/-- **The comparison lemma along a trajectory.**  Let `σ` be the class `KL` bound that
`classK_dini_bound` attaches to a class `K` function `α`.  If `v(τ) = V(τ, x(τ))` stays in
`[0, d)` on `[t₀, t]` and `V̇ ≤ -α(V)` there, then `V(t, x(t)) ≤ σ(V(t₀, x(t₀)), t - t₀)`.

This only checks the side conditions of `classK_dini_bound`: `v` is continuous, its Dini
derivative is the derivative along the system, and its difference quotients are bounded. -/
private lemma comp_trajectory_le_classKL {s : ContinuousSystem ℝⁿ Unit Y} {V : ℝ → ℝⁿ → ℝ}
    (hV : Differentiable ℝ (Function.uncurry V))
    {d e : ℝ} {α : ClassK d e} {σ : ClassKL d}
    (hσ : ∀ {t₀ t : ℝ}, t₀ ≤ t → ∀ (v : ℝ → ℝ), ContinuousOn v (Icc t₀ t) →
        v t₀ ∈ Ico 0 d →
        (∀ s ∈ Ico t₀ t, v s ∈ Ico 0 d) →
        (∀ s ∈ Ico t₀ t, D⁺ v s ≤ -α.toFun (v s)) →
        (∀ s ∈ Ico t₀ t,
            IsBoundedUnder (· ≤ ·) (𝓝[>] 0) (fun h => (v (s + h) - v s) / h)) →
        v t ≤ σ.toFun (v t₀) (t - t₀))
    {x : ℝ → ℝⁿ} {t₀ t₁ t : ℝ} (hx : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁))
    (ht : t ∈ Icc t₀ t₁)
    (hv_range : ∀ τ ∈ Icc t₀ t, V τ (x τ) ∈ Ico 0 d)
    (hlie : ∀ τ ∈ Ico t₀ t, s.lieDerivative V τ (x τ) () ≤ -α.toFun (V τ (x τ))) :
    V t (x t) ≤ σ.toFun (V t₀ (x t₀)) (t - t₀) := by
  -- Before `t ≤ t₁`, the derivative within `[t₀, t₁]` is a right derivative.
  have hderiv : ∀ τ ∈ Ico t₀ t, HasDerivWithinAt (fun u => V u (x u))
      (s.lieDerivative V τ (x τ) ()) (Ici τ) τ := fun τ hτ =>
    (hx.hasDerivWithinAt_lieDerivative hV ⟨hτ.1, hτ.2.le.trans ht.2⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hτ.1, hτ.2.trans_le ht.2⟩)
  have hv_cont : ContinuousOn (fun u => V u (x u)) (Icc t₀ t) :=
    hV.continuous.comp_continuousOn (continuousOn_id.prodMk
      ((IsIntegralCurveOn.continuousOn hx).mono (Icc_subset_Icc_right ht.2)))
  exact hσ ht.1 (fun u => V u (x u)) hv_cont (hv_range t₀ ⟨le_rfl, ht.1⟩)
    (fun τ hτ => hv_range τ (Ico_subset_Icc_self hτ))
    (fun τ hτ => by rw [diniDerivRight_of_hasDerivWithinAt (hderiv τ hτ)]; exact hlie τ hτ)
    (fun τ hτ => (hderiv τ hτ).tendsto_forward_slope.isBoundedUnder_le)

/-! ## Lyapunov's uniform asymptotic stability theorem -/

/-- **Lyapunov's uniform asymptotic stability theorem**: a strict uniform Lyapunov function
certifies uniform asymptotic stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.9.  Khalil's two "moreover" clauses
are not part of this conclusion: the explicit class `KL` bound, which the proof constructs, and
the global case, when `D` is the whole space and `W₁` is radially unbounded. -/
@[blueprint "thm:continuousSystem-isStrictUniformLyapunovFunction-uniformlyAsymptoticallyStable"
  (title := "Lyapunov's uniform asymptotic stability theorem")
  (statement := /-- If $V$ is a strict uniform Lyapunov function for $x_{\mathrm{eq}}$
    (\cref{def:continuousSystem-isStrictUniformLyapunovFunction}) on a system with state space
    $\mathbb{R}^n$, then $x_{\mathrm{eq}}$ is uniformly asymptotically stable
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}).

    A strictly negative $\dot V$ alone would not do: $W_3$ must be bounded away from zero on
    each annulus, which is exactly what positive definiteness of a function of $x$ alone buys.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.9.  Khalil's two
    ``moreover'' clauses are not part of this conclusion: the explicit class $\mathcal{KL}$
    bound, which the proof constructs, and the global case. -/)
  (proof := /-- Uniform stability is
    \cref{thm:continuousSystem-isUniformLyapunovFunction-uniformlyStable}.  For convergence,
    take class $\mathcal{K}$ bounds $\alpha_1, \alpha_2, \alpha_3$ for $W_1, W_2, W_3$ on a ball
    in the region of the certificate, and the trapping radius $c$ of that proof.  Along a
    trajectory from the $c$-ball,
    $\dot V \le -W_3(x) \le -\alpha_3(\|x - x_{\mathrm{eq}}\|) \le -\alpha_3(\alpha_2^{-1}(V))$,
    so $v(t) = V(t, x(t))$ satisfies $D^+ v \le -\alpha(v)$ with
    $\alpha = \alpha_3 \circ \alpha_2^{-1}$ of class $\mathcal{K}$.
    \cref{thm:classK-dini-bound} gives a class $\mathcal{KL}$ $\sigma$ with
    $v(t) \le \sigma(v(t_0), t - t_0)$; unwinding the sandwich,
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le
        \alpha_1^{-1}\bigl(\sigma(\alpha_2(\|x(t_0) - x_{\mathrm{eq}}\|), t - t_0)\bigr),
    \]
    a class $\mathcal{KL}$ bound.  Conclude by
    \cref{lem:continuousSystem-hasUniformConvergenceTime-of-classKL}. -/)]
theorem IsStrictUniformLyapunovFunction.uniformlyAsymptoticallyStable [NeZero n]
    {s : ContinuousSystem ℝⁿ Unit Y} {V : ℝ → ℝⁿ → ℝ} {x_eq : ℝⁿ} {D : Set ℝⁿ}
    (hV : s.IsStrictUniformLyapunovFunction V x_eq D) :
    s.UniformlyAsymptoticallyStable x_eq := by
  /- Along a trajectory `v(t) = V(t, x(t))` obeys `D⁺v ≤ -α₃(α₂⁻¹(v))`, so the comparison lemma
     bounds it by a class KL `σ(v(t₀), t - t₀)`; the sandwich turns this into the class KL
     bound `‖x(t) - x_eq‖ ≤ α₁⁻¹(σ(α₂(‖x(t₀) - x_eq‖), t - t₀))`. -/
  refine ⟨hV.toIsUniformLyapunovFunction.uniformlyStable, ?_⟩
  obtain ⟨W₁, hW₁, hV_lb⟩ := hV.lower
  obtain ⟨W₂, hW₂, hV_ub⟩ := hV.upper
  obtain ⟨W₃, hW₃, hV_strict⟩ := hV.strict
  -- Step 1. A ball in `D`, and class `K` bounds for `W₁`, `W₂`, `W₃` on it.
  obtain ⟨r, hr, hrD⟩ := nhds_basis_closedBall.mem_iff.mp hV.nhds
  have hD : ∀ y : ℝⁿ, ‖y - x_eq‖ ≤ r → y ∈ D := fun y hy => hrD (mem_closedBall_iff_norm.mpr hy)
  obtain ⟨b₁, _, α₁, _, hW₁_bd⟩ := LyapunovClassKBounds hr hrD hW₁
  obtain ⟨_, b₂, _, α₂, hW₂_bd⟩ := LyapunovClassKBounds hr hrD hW₂
  obtain ⟨_, _, α₃, _, hW₃_bd⟩ := LyapunovClassKBounds hr hrD hW₃
  -- Step 2. The level `d` and trapping radius `c = α₂⁻¹(d)` of the uniform-stability proof.
  obtain ⟨d, hd_pos, hd_lt_b₁, hd_lt_b₂, hc_pos, hc_lt_r, h_α₂_c⟩ :=
    exists_sandwich_level α₁.hb α₂
  set c := α₂.invFun d
  have hV_lt_d : ∀ t : ℝ, 0 ≤ t → ∀ y : ℝⁿ, ‖y - x_eq‖ < c → V t y < d := fun t ht y hy =>
    lt_level_of_norm_lt hV_ub hrD (fun y hy => (hW₂_bd y hy).2) hc_lt_r h_α₂_c ht hy
  -- Step 3. A trajectory from the `c`-ball never leaves the `r`-ball ...
  have h_in_ball : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → ℝⁿ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < r := fun t₀ ht₀ t₁ x hx h_init =>
    norm_lt_of_trapped hV.toIsLyapunovFunction hV_lb hrD (fun y hy => (hW₁_bd y hy).1)
      ⟨hd_pos.le, hd_lt_b₁⟩ hx ht₀ (h_init.trans hc_lt_r) (hV_lt_d t₀ ht₀ _ h_init)
  -- ... and keeps `V` in `[0, d)`: it starts below `d` and does not increase.
  have hV_range : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → ℝⁿ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
        ∀ t ∈ Icc t₀ t₁, V t (x t) ∈ Ico 0 d := fun t₀ ht₀ t₁ x hx h_init t ht => by
    have h_ball := h_in_ball t₀ ht₀ t₁ x hx h_init
    have h_anti := hx.antitoneOn_of_lieDerivative_nonpos hV.differentiable fun u hu =>
      hV.lie_nonpos u (ht₀.trans hu.1.le) (x u) (hD _ (h_ball u (Ioo_subset_Icc_self hu)).le)
    have hx_D : x t ∈ D := hD _ (h_ball t ht).le
    exact ⟨(hW₁.nonneg hx_D).trans (hV_lb t (ht₀.trans ht.1) _ hx_D),
      (h_anti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1).trans_lt (hV_lt_d t₀ ht₀ _ h_init)⟩
  -- Step 4. The comparison function `α₃ ∘ α₂⁻¹` on `[0, d)` and its class KL bound `σ`.
  have h_α : ∃ α : ClassK d (α₃.toFun c), ∀ y ∈ Ico 0 d, α.toFun y = α₃.toFun (α₂.invFun y) := by
    -- Compose `α₂⁻¹ : [0, d) → [0, c)` with `α₃` restricted to `[0, c)`.  As `c` is by
    -- definition `α₂⁻¹(d)`, the two domains match definitionally, so `ClassK.comp` needs no
    -- cast and the composite agrees with `α₃ ∘ α₂⁻¹` by `rfl`.
    let α₂_inv_res := α₂.symm.restrict hd_pos hd_lt_b₂
    let α₃_res : ClassK (α₂.symm.toFun d) (α₃.toFun c) := α₃.restrict hc_pos hc_lt_r
    exact ⟨ClassK.comp α₃_res α₂_inv_res, fun _ _ => rfl⟩
  obtain ⟨α, hα_eq⟩ := h_α
  obtain ⟨σ, hσ_zero, hσ⟩ := classK_dini_bound α
  -- In the `r`-ball, `V̇ ≤ -W₃(y) ≤ -α₃(‖y - x_eq‖) ≤ -α₃(α₂⁻¹(V))`.
  have hlie_comp : ∀ t : ℝ, 0 ≤ t → ∀ y : ℝⁿ, ‖y - x_eq‖ < r → V t y ∈ Ico 0 d →
      s.lieDerivative V t y () ≤ -α.toFun (V t y) := fun t ht y hy hVy => by
    have h_le : α.toFun (V t y) ≤ α₃.toFun ‖y - x_eq‖ := by
      rw [hα_eq _ hVy]
      exact α₂.toFun_invFun_le α₃ ⟨norm_nonneg _, hy⟩ ⟨hVy.1, hVy.2.trans hd_lt_b₂⟩
        ((hV_ub t ht y (hD y hy.le)).trans (hW₂_bd y hy).2)
    linarith [hV_strict t ht y (hD y hy.le), (hW₃_bd y hy).1]
  -- Step 5. The class KL bound `β(ρ, s) = α₁⁻¹(σ(α₂(ρ), s))`.
  obtain ⟨β, hβ_eq⟩ := ClassKL.exists_comp_sandwich α₁ α₂ hσ_zero hc_pos hc_lt_r h_α₂_c hd_lt_b₁
  -- Step 6. Every trajectory from the `c`-ball obeys `β`.
  refine ⟨c / 2, half_pos hc_pos, hasUniformConvergenceTime_of_classKL β (half_lt_self hc_pos) ?_⟩
  intro t₀ ht₀ t₁ x hx h_init t ht
  have h_ball := h_in_ball t₀ ht₀ t₁ x hx h_init
  have h_range := hV_range t₀ ht₀ t₁ x hx h_init
  have h_xt_lt_r : ‖x t - x_eq‖ < r := h_ball t ht
  have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
  have ht₀_mem : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  -- `V(t, x(t)) ≤ σ(V(t₀, x(t₀)), t - t₀)`, by the comparison lemma.
  have h_σ_bound : V t (x t) ≤ σ.toFun (V t₀ (x t₀)) (t - t₀) :=
    comp_trajectory_le_classKL hV.differentiable hσ hx ht
      (fun τ hτ => h_range τ ⟨hτ.1, hτ.2.trans ht.2⟩)
      (fun τ hτ => hlie_comp τ (ht₀.trans hτ.1) _ (h_ball τ ⟨hτ.1, hτ.2.le.trans ht.2⟩)
        (h_range τ ⟨hτ.1, hτ.2.le.trans ht.2⟩))
  -- `V(t₀, x(t₀))` and `α₂(‖x(t₀) - x_eq‖)` lie in `[0, d)`, and `σ(·, t - t₀)` keeps `[0, d)`.
  have hV_t₀_mem : V t₀ (x t₀) ∈ Ico 0 d := h_range t₀ ht₀_mem
  have h_α₂_t₀_mem : α₂.toFun ‖x t₀ - x_eq‖ ∈ Ico 0 d :=
    α₂.toFun_mem_Ico hc_lt_r h_α₂_c ⟨norm_nonneg _, h_init⟩
  have h_σ_mem : σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) ∈ Ico 0 d :=
    σ.toFun_mem_Ico hσ_zero h_α₂_t₀_mem ht_sub
  -- `α₁(‖x(t) - x_eq‖) ≤ W₁ ≤ V ≤ σ(V(t₀, x(t₀)), t - t₀) ≤ σ(α₂(‖x(t₀) - x_eq‖), t - t₀)`.
  have h_x₀_lt_r : ‖x t₀ - x_eq‖ < r := h_init.trans hc_lt_r
  have h_chain : α₁.toFun ‖x t - x_eq‖ ≤ σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) :=
    calc α₁.toFun ‖x t - x_eq‖
      _ ≤ W₁ (x t) := (hW₁_bd (x t) h_xt_lt_r).1
      _ ≤ V t (x t) := hV_lb t (ht₀.trans ht.1) (x t) (hD _ h_xt_lt_r.le)
      _ ≤ σ.toFun (V t₀ (x t₀)) (t - t₀) := h_σ_bound
      _ ≤ σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) :=
            (σ.strict_mono_r (t - t₀) ht_sub).monotoneOn hV_t₀_mem h_α₂_t₀_mem
              ((hV_ub t₀ ht₀ _ (hD _ h_x₀_lt_r.le)).trans (hW₂_bd _ h_x₀_lt_r).2)
  -- Invert `α₁`, which is increasing on `[0, b₁) ⊇ [0, d)`.
  have h_α₁_mem : α₁.toFun ‖x t - x_eq‖ ∈ Ico 0 b₁ := α₁.maps_to ⟨norm_nonneg _, h_xt_lt_r⟩
  have h_σ_mem_b₁ : σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀) ∈ Ico 0 b₁ :=
    ⟨h_σ_mem.1, h_σ_mem.2.trans hd_lt_b₁⟩
  calc ‖x t - x_eq‖
      = α₁.invFun (α₁.toFun ‖x t - x_eq‖) := (α₁.left_inv ⟨norm_nonneg _, h_xt_lt_r⟩).symm
    _ ≤ α₁.invFun (σ.toFun (α₂.toFun ‖x t₀ - x_eq‖) (t - t₀)) :=
        (α₁.inv_mono_iff h_α₁_mem h_σ_mem_b₁).mpr h_chain
    _ = β.toFun ‖x t₀ - x_eq‖ (t - t₀) := (hβ_eq _ _).symm

end Euclidean

end ContinuousSystem
