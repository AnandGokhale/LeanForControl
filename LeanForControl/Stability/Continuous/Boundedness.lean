import LeanForControl.Stability.Continuous.LyapunovTheorems
import Architect

/-!
# `Stability.Continuous.Boundedness` — ultimate bounds from Lyapunov-like functions

A function `V` sandwiched between class `K` functions of `‖x - x_c‖`, whose derivative along the
system is negative only *outside* a ball of radius `μ`, need not certify stability of anything:
inside that ball the trajectories may do as they please.  It still bounds them: they reach a
neighbourhood of `x_c` of size `α₁⁻¹(α₂(μ))` in a uniform time and stay there, and before that they
decay like a class `KL` function.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.8, Theorem 4.18, proved in his
Appendix C.9.

## Main results

* `exists_classKL_ultimateBound_of_lyapunov` — Khalil's Theorem 4.18, with its two estimates
  (4.42) and (4.43) combined into one:
  `‖x(t) - x_c‖ ≤ max (β(‖x(t₀) - x_c‖, t - t₀)) (α₁⁻¹(α₂(μ)))`.
* `uniformlyBounded_of_lyapunov` — the trajectories are uniformly bounded.
* `uniformlyUltimatelyBounded_of_lyapunov` — given forward completeness, they are uniformly
  ultimately bounded with ultimate bound `α₁⁻¹(α₂(μ))`.
* `exists_classKLGlobal_ultimateBound_of_lyapunov`, `globallyUniformlyBounded_of_lyapunov`,
  `globallyUniformlyUltimatelyBounded_of_lyapunov` — the global case, Khalil's "moreover" clause.

## The argument

Write `v(t) = V(t, x(t))`, `η = α₂(μ)` and `d = α₂(c)`, where `c` is the initial radius.

* **Above `η`, `v` falls.**  `v > η` forces `‖x - x_c‖ > μ`, where `V̇ ≤ -W₃ ≤ 0`.  So the
  trajectory never reaches the sphere on which `α₁ = d`
  (`IsRightTrajectoryOn.trapped_in_ball`): it stays in the ball where the sandwich holds.
* **Decay to `η`.**  There `V̇ ≤ -α₃(‖x - x_c‖) ≤ -α₃(α₂⁻¹(v))`, so
  `v(t) ≤ max (σ(v(t₀), t - t₀)) η` for a class `KL` function `σ`
  (`ClassK.exists_classKL_bound_above_level`).

The sandwich turns this into the bound on the state.

## Differences from Khalil

* The class `K` functions are defined on `[0, r)`, with ranges `[0, b₁)` and `[0, b₂)`, so the
  ball on which the sandwich holds is open.  Khalil's level `α₁(r)` becomes `b₁`, and his
  conditions `μ < α₂⁻¹(α₁(r))` and `‖x(t₀)‖ ≤ α₂⁻¹(α₁(r))` become the choice of an initial
  radius `c` with `μ < c` and `α₂(c) < b₁`, and `‖x(t₀) - x_c‖ < c`.
* `μ = 0` is allowed, recovering the class `KL` bound of Theorem 4.9.
* Khalil's time `T` depends on `x(t₀)`; the combined estimate gives one depending only on a bound
  for `‖x(t₀) - x_c‖`, which is what uniform ultimate boundedness asks for.
* In the global case Khalil takes one class `K` lower bound for `W₃` on all of `E`, which need
  not exist: a positive definite `W₃` may tend to `0` at infinity.  The global class `KL`
  function is instead assembled from the local ones of a sequence of balls
  (`ClassKLGlobal.exists_ge_min_of_decay`).
* The point `x_c` is general; Khalil places it at the origin.
-/

open Set Filter Topology Metric

namespace ContinuousSystem

universe u

variable {Y : Type u} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An **ultimate bound Lyapunov function**: `V` is differentiable on the `r`-ball about `x_c`,
sandwiched there between `α₁(‖x - x_c‖)` and `α₂(‖x - x_c‖)`, and decreases at least as fast as
`W₃` outside the `μ`-ball.  It certifies an ultimate bound `α₁⁻¹(α₂(μ))`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18, (4.40)–(4.41). -/
@[blueprint "def:continuousSystem-isUltimateBoundLyapunovFunction"
  (title := "Ultimate bound Lyapunov function")
  (statement := /-- Let $\alpha_1 : [0, r) \to [0, b_1)$ and $\alpha_2 : [0, r) \to [0, b_2)$ be
    class $\mathcal{K}$, $W_3 : \mathbb{R}^n \to \mathbb{R}$ and $\mu \ge 0$.  A function
    $V : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}$ is an \emph{ultimate bound Lyapunov
    function} for the system about $x_c$ if, for all $t \ge 0$ and $\|x - x_c\| < r$, $V$ is
    differentiable at $(t, x)$ and
    \[
      \alpha_1(\|x - x_c\|) \le V(t, x) \le \alpha_2(\|x - x_c\|), \qquad
      \dot V(t, x) \le -W_3(x) \quad \text{for } \mu \le \|x - x_c\|.
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.18, (4.40)--(4.41). -/)]
structure IsUltimateBoundLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ)
    (x_c : E) {r b₁ b₂ : ℝ} (α₁ : ClassK r b₁) (α₂ : ClassK r b₂) (W₃ : E → ℝ) (μ : ℝ) :
    Prop where
  /-- `V` is differentiable on the ball. -/
  differentiableAt : ∀ t : ℝ, 0 ≤ t → ∀ y : E, ‖y - x_c‖ < r →
    DifferentiableAt ℝ (Function.uncurry V) (t, y)
  /-- `V` is sandwiched between class `K` functions of `‖x - x_c‖`. -/
  sandwich : ∀ t : ℝ, 0 ≤ t → ∀ y : E, ‖y - x_c‖ < r →
    α₁.toFun ‖y - x_c‖ ≤ V t y ∧ V t y ≤ α₂.toFun ‖y - x_c‖
  /-- `V̇ ≤ -W₃` outside the `μ`-ball. -/
  decrease : ∀ t : ℝ, 0 ≤ t → ∀ y : E, μ ≤ ‖y - x_c‖ → ‖y - x_c‖ < r →
    s.lieDerivative V t y () ≤ -W₃ y

/-- A **global ultimate bound Lyapunov function**: the conditions of
`IsUltimateBoundLyapunovFunction` on all of `E`, with `α₁, α₂` of class `K∞`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18, global case. -/
@[blueprint "def:continuousSystem-isGlobalUltimateBoundLyapunovFunction"
  (title := "Global ultimate bound Lyapunov function")
  (statement := /-- With $\alpha_1, \alpha_2$ class $\mathcal{K}_\infty$, the conditions of
    \cref{def:continuousSystem-isUltimateBoundLyapunovFunction} for all $t \ge 0$ and all
    $x \in \mathbb{R}^n$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.18, global case. -/)]
structure IsGlobalUltimateBoundLyapunovFunction (s : ContinuousSystem E Unit Y) (V : ℝ → E → ℝ)
    (x_c : E) (α₁ α₂ : ClassKInfty) (W₃ : E → ℝ) (μ : ℝ) : Prop where
  /-- `V` is differentiable. -/
  differentiableAt : ∀ t : ℝ, 0 ≤ t → ∀ y : E, DifferentiableAt ℝ (Function.uncurry V) (t, y)
  /-- `V` is sandwiched between class `K∞` functions of `‖x - x_c‖`. -/
  sandwich : ∀ t : ℝ, 0 ≤ t → ∀ y : E,
    α₁.toFun ‖y - x_c‖ ≤ V t y ∧ V t y ≤ α₂.toFun ‖y - x_c‖
  /-- `V̇ ≤ -W₃` outside the `μ`-ball. -/
  decrease : ∀ t : ℝ, 0 ≤ t → ∀ y : E, μ ≤ ‖y - x_c‖ → s.lieDerivative V t y () ≤ -W₃ y

/-- **Khalil's ultimate boundedness theorem.**  Let `V` be an ultimate bound Lyapunov function
on the `r`-ball, with `W₃` positive definite.  Then from the `c`-ball, for any `c` with
`μ < c < r` and `α₂(c) < b₁`, the trajectories obey
`‖x(t) - x_c‖ ≤ max (β(‖x(t₀) - x_c‖, t - t₀)) (α₁⁻¹(α₂(μ)))` for a class `KL` function `β`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18. -/
@[blueprint "thm:continuousSystem-exists-classKL-ultimateBound-of-lyapunov"
  (title := "Ultimate boundedness theorem")
  (statement := /-- Let the state space be $\mathbb{R}^n$, $V$ an ultimate bound Lyapunov
    function about $x_c$ with data $\alpha_1, \alpha_2, W_3, \mu$
    (\cref{def:continuousSystem-isUltimateBoundLyapunovFunction}), where $W_3$ is positive
    definite about $x_c$ on the closed $r$-ball (\cref{def:isPositiveDefiniteOn}) and
    $0 \le \mu < c$, where $c < r$ and $\alpha_2(c) < b_1$.  Then there is a class
    $\mathcal{KL}$ function $\beta$ on $[0, c)$, depending only on $\alpha_1, \alpha_2, W_3$
    and $c$ --- not on the system, $V$ or $\mu$ --- such that every right trajectory
    (\cref{def:continuousSystem-isRightTrajectoryOn}) on a segment $[t_0, t_1]$, $t_0 \ge 0$, with
    $\|x(t_0) - x_c\| < c$ satisfies
    \[
      \|x(t) - x_c\| \le \max\bigl\{\beta(\|x(t_0) - x_c\|, t - t_0),\;
        \alpha_1^{-1}(\alpha_2(\mu))\bigr\} \qquad \forall\, t \in [t_0, t_1].
    \]
    Khalil's estimates (4.42) and (4.43) are the two branches of the maximum.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.18.  Differences:
    \begin{itemize} \item The sandwich holds on an open ball; Khalil's level $\alpha_1(r)$
    becomes $b_1$, and the initial states form the open $c$-ball. \item $\mu = 0$ is allowed.
    \item $\beta(\rho, s) \le \alpha_1^{-1}(\alpha_2(\rho))$ is part of the conclusion. The
    global case is \cref{thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov}.
    \end{itemize} -/)
  (proof := /-- Let $v(t) = V(t, x(t))$, $\eta = \alpha_2(\mu)$ and $d = \alpha_2(c)$.  If
    $v > \eta$ then $\alpha_2(\|x - x_c\|) \ge v > \alpha_2(\mu)$, so $\|x - x_c\| > \mu$ and
    $\dot v \le -W_3 \le 0$.  The trajectory therefore never reaches the sphere
    $\alpha_1(\|x - x_c\|) = d$: up to the first time it did, $v$ could only fall while above
    $\eta$, so it would be at most $\max\{v(t_0), \eta\} < d$
    (\cref{lem:le-max-of-hasDerivWithinAt-nonpos-above}), while on the sphere $v \ge d$.

    Bound $W_3$ below by a class $\mathcal{K}$ $\alpha_3$ (\cref{thm:lyapunov-class-K-bounds}).
    Above $\eta$, $\dot v \le -\alpha_3(\|x - x_c\|) \le -\alpha_3(\alpha_2^{-1}(v))$, so
    \cref{thm:classK-bound-above-level} gives
    $v(t) \le \max\{\sigma(\alpha_2(\|x(t_0) - x_c\|), t - t_0), \eta\}$.  Apply the increasing
    $\alpha_1^{-1}$ and set $\beta(\rho, s) = \alpha_1^{-1}(\sigma(\alpha_2(\rho), s))$. -/)]
theorem exists_classKL_ultimateBound_of_lyapunov [Nontrivial E] {x_c : E} {r b₁ b₂ c : ℝ}
    (α₁ : ClassK r b₁) (α₂ : ClassK r b₂) {W₃ : E → ℝ}
    (hW₃ : IsPositiveDefiniteOn W₃ x_c (closedBall x_c r))
    (hc_pos : 0 < c) (hcr : c < r) (hc : α₂.toFun c < b₁) :
    ∃ β : ClassKL c, (∀ ρ ∈ Ico 0 c, ∀ θ : ℝ, 0 ≤ θ → β.toFun ρ θ ≤ α₁.invFun (α₂.toFun ρ)) ∧
      ∀ {Y : Type u} {s : ContinuousSystem E Unit Y} {V : ℝ → E → ℝ} {μ : ℝ},
        s.IsUltimateBoundLyapunovFunction V x_c α₁ α₂ W₃ μ → 0 ≤ μ → μ < c →
        ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
          s.IsRightTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_c‖ < c →
            ∀ t ∈ Icc t₀ t₁,
              ‖x t - x_c‖ ≤ max (β.toFun ‖x t₀ - x_c‖ (t - t₀)) (α₁.invFun (α₂.toFun μ)) := by
  -- Step 1. The level `d = α₂(c) < b₁`, and `α₃ ≤ W₃` on the ball.
  have hc_mem : c ∈ Ico 0 r := ⟨hc_pos.le, hcr⟩
  set d := α₂.toFun c
  have hd_pos : 0 < d := (α₂.pos_iff hc_mem).mpr hc_pos
  have hd_mem₁ : d ∈ Ico 0 b₁ := ⟨hd_pos.le, hc⟩
  obtain ⟨_, _, α₃, _, hW₃_bd⟩ := hW₃.exists_classK_bounds (hc_pos.trans hcr) subset_rfl
  -- Step 2. The comparison function `α = α₃ ∘ α₂⁻¹` on `[0, d)`, its class KL bound `σ`, and
  -- `β(ρ, s) = α₁⁻¹(σ(α₂(ρ), s))`.  None of this involves the system, `V` or `μ`, so neither
  -- does `β`.
  let α := α₃.compSymm α₂ hc_pos hcr
  obtain ⟨σ, hσ_zero, hσ⟩ := α.exists_classKL_bound_above_level
  obtain ⟨β, hβ_eq⟩ := ClassKL.exists_comp_sandwich α₁ α₂ hσ_zero hc_pos hcr rfl hc
  -- `β` never exceeds its value at elapsed time `0`, which is at most `α₁⁻¹(α₂(ρ))`, since
  -- `σ(y, θ) ≤ σ(y, 0) ≤ y`.
  have hβ_le : ∀ ρ ∈ Ico 0 c, ∀ θ : ℝ, 0 ≤ θ → β.toFun ρ θ ≤ α₁.invFun (α₂.toFun ρ) :=
    fun ρ hρ θ hθ => by
    have hy := α₂.toFun_mem_Ico hcr rfl hρ
    have hσ_mem := σ.toFun_mem_Ico hσ_zero hy hθ
    rw [hβ_eq]
    exact (α₁.inv_mono_iff ⟨hσ_mem.1, hσ_mem.2.trans hc⟩ ⟨hy.1, hy.2.trans hc⟩).mpr
      ((σ.anti_s_mono hy (mem_Ici.mpr le_rfl) (mem_Ici.mpr hθ) hθ).trans (hσ_zero _ hy))
  refine ⟨β, hβ_le, fun {Y s V μ} ⟨hV, hV_bd, hlie⟩ hμ hμc t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
  -- The ultimate level `η = α₂(μ) < d`.
  have hμ_mem : μ ∈ Ico 0 r := ⟨hμ, hμc.trans hcr⟩
  set η := α₂.toFun μ
  have hη_lt_d : η < d := α₂.strict_mono hμ_mem hc_mem hμc
  -- Above `η` in the ball, `α₂(‖y - x_c‖) ≥ V > α₂(μ)`, so `y` is outside the `μ`-ball ...
  have h_far : ∀ τ : ℝ, 0 ≤ τ → ∀ y : E, ‖y - x_c‖ < r → η < V τ y → μ < ‖y - x_c‖ :=
    fun τ hτ y hy hηV =>
      (α₂.strict_mono_iff hμ_mem ⟨norm_nonneg _, hy⟩).mp (hηV.trans_le (hV_bd τ hτ y hy).2)
  -- ... where `V̇ ≤ -W₃(y) ≤ 0` ...
  have h_nonpos : ∀ τ : ℝ, 0 ≤ τ → ∀ y : E, ‖y - x_c‖ < r → η < V τ y →
      s.lieDerivative V τ y () ≤ 0 := fun τ hτ y hy hηV => by
    linarith [hlie τ hτ y (h_far τ hτ y hy hηV).le hy,
      hW₃.nonneg (mem_closedBall_iff_norm.mpr hy.le)]
  -- ... and `V̇ ≤ -W₃(y) ≤ -α₃(‖y - x_c‖) ≤ -α₃(α₂⁻¹(V)) = -α(V)`.
  have h_decay : ∀ τ : ℝ, 0 ≤ τ → ∀ y : E, ‖y - x_c‖ < r → η < V τ y →
      s.lieDerivative V τ y () ≤ -α.toFun (V τ y) := fun τ hτ y hy hηV => by
    have hy_mem : ‖y - x_c‖ ∈ Ico 0 r := ⟨norm_nonneg _, hy⟩
    have hV_up := (hV_bd τ hτ y hy).2
    -- `α(V) = α₃(α₂⁻¹(V)) ≤ α₃(‖y - x_c‖)`.
    have h_α_le : α.toFun (V τ y) ≤ α₃.toFun ‖y - x_c‖ := by
      rw [ClassK.compSymm_toFun]
      exact α₂.toFun_invFun_le α₃ hy_mem
        (α₁.mem_Ico_of_sandwich α₂ hy_mem (hV_bd τ hτ y hy).1 hV_up) hV_up
    linarith [hlie τ hτ y (h_far τ hτ y hy hηV).le hy, (hW₃_bd y hy).1]
  -- Step 3. `v(τ) = V(τ, x(τ))` starts below `d`.
  have hx₀_mem : ‖x t₀ - x_c‖ ∈ Ico 0 r := ⟨norm_nonneg _, h_init.trans hcr⟩
  have hv₀_up : V t₀ (x t₀) ≤ α₂.toFun ‖x t₀ - x_c‖ := (hV_bd t₀ ht₀ _ hx₀_mem.2).2
  have h_α₂₀_mem : α₂.toFun ‖x t₀ - x_c‖ ∈ Ico 0 d :=
    α₂.toFun_mem_Ico hcr rfl ⟨norm_nonneg _, h_init⟩
  have h_max_lt_d : max (V t₀ (x t₀)) η < d := max_lt (hv₀_up.trans_lt h_α₂₀_mem.2) hη_lt_d
  -- Step 4. Trapping: the trajectory stays inside the `r'`-sphere, `r' = α₁⁻¹(d) < r`, on which
  -- `V ≥ α₁(r') = d`.
  have hr'_mem : α₁.invFun d ∈ Ico 0 r := α₁.inv_maps_to hd_mem₁
  have h_trap : ∀ τ ∈ Icc t₀ t₁, ‖x τ - x_c‖ < r := fun τ hτ =>
    (hx.trapped_in_ball
      (fun u hu hu_norm => hV u (ht₀.trans hu.1) _ (hu_norm.trans_lt hr'_mem.2))
      ((α₁.strict_mono_iff hx₀_mem hr'_mem).mp (by
        rw [α₁.right_inv hd_mem₁]
        exact (hV_bd t₀ ht₀ _ hx₀_mem.2).1.trans_lt (lt_of_le_of_lt (le_max_left _ _) h_max_lt_d)))
      h_max_lt_d
      (fun u hu hu_norm => by
        rw [← α₁.right_inv hd_mem₁, ← hu_norm]
        exact (hV_bd u (ht₀.trans hu.1) _ (hu_norm ▸ hr'_mem.2)).1)
      (fun u hu hu_norm => h_nonpos u (ht₀.trans hu.1) _ (hu_norm.trans_lt hr'_mem.2))
      τ hτ).trans hr'_mem.2
  -- Inside the ball `V` is differentiable, so `v` is continuous with right derivative `V̇`.
  have hV_traj : ∀ τ ∈ Icc t₀ t₁, DifferentiableAt ℝ (Function.uncurry V) (τ, x τ) :=
    fun τ hτ => hV τ (ht₀.trans hτ.1) _ (h_trap τ hτ)
  have hv_cont : ContinuousOn (fun τ => V τ (x τ)) (Icc t₀ t₁) :=
    hx.1.comp_uncurry_of_differentiableAt hV_traj
  have hv_deriv : ∀ τ ∈ Ico t₀ t₁, HasDerivWithinAt (fun u => V u (x u))
      (s.lieDerivative V τ (x τ) ()) (Ici τ) τ := fun τ hτ =>
    (hx.hasDerivWithinAt_Ici hτ).hasDerivWithinAt_lieDerivative
      (hV_traj τ (Ico_subset_Icc_self hτ))
  -- Step 5. Inside the ball `v` falls while above `η`, so it stays in `[0, d)`, and decays to `η`:
  -- `v(t) ≤ max (σ(v(t₀), t - t₀)) η`.
  have hv_max : ∀ τ ∈ Icc t₀ t₁, V τ (x τ) ≤ max (V t₀ (x t₀)) η :=
    le_max_of_hasDerivWithinAt_nonpos_above hv_cont hv_deriv fun τ hτ =>
      h_nonpos τ (ht₀.trans hτ.1) _ (h_trap τ (Ico_subset_Icc_self hτ))
  have hv_mem : ∀ τ ∈ Icc t₀ t₁, V τ (x τ) ∈ Ico 0 d := fun τ hτ =>
    ⟨(α₁.maps_to ⟨norm_nonneg _, h_trap τ hτ⟩).1.trans
      (hV_bd τ (ht₀.trans hτ.1) _ (h_trap τ hτ)).1, (hv_max τ hτ).trans_lt h_max_lt_d⟩
  have hv_t : V t (x t) ≤ max (σ.toFun (V t₀ (x t₀)) (t - t₀)) η :=
    hσ ht.1 (hv_cont.mono (Icc_subset_Icc_right ht.2))
      (fun τ hτ => hv_deriv τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
      (fun τ hτ => hv_mem τ ⟨hτ.1, hτ.2.trans ht.2⟩)
      (fun τ hτ => h_decay τ (ht₀.trans hτ.1) _ (h_trap τ ⟨hτ.1, hτ.2.le.trans ht.2⟩))
  -- Step 6. Unwind the sandwich: `α₁(‖x(t) - x_c‖) ≤ v(t) ≤ max (σ(α₂(‖x(t₀) - x_c‖), t - t₀)) η`,
  -- and `α₁⁻¹` is increasing on `[0, b₁) ⊇ [0, d)`, so it passes through the maximum.
  have ht_sub : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
  set S := σ.toFun (α₂.toFun ‖x t₀ - x_c‖) (t - t₀)
  have hS_mem : S ∈ Ico 0 b₁ :=
    let h := σ.toFun_mem_Ico hσ_zero h_α₂₀_mem ht_sub; ⟨h.1, h.2.trans hc⟩
  have hη_mem : η ∈ Ico 0 b₁ := ⟨(α₂.maps_to hμ_mem).1, hη_lt_d.trans hc⟩
  have hxt_mem : ‖x t - x_c‖ ∈ Ico 0 r := ⟨norm_nonneg _, h_trap t ht⟩
  have h_α₁t : α₁.toFun ‖x t - x_c‖ ≤ max S η :=
    calc α₁.toFun ‖x t - x_c‖
        ≤ V t (x t) := (hV_bd t (ht₀.trans ht.1) _ hxt_mem.2).1
      _ ≤ max (σ.toFun (V t₀ (x t₀)) (t - t₀)) η := hv_t
      _ ≤ max S η := max_le_max ((σ.strict_mono_r _ ht_sub).monotoneOn
          (hv_mem t₀ ⟨le_rfl, ht.1.trans ht.2⟩) h_α₂₀_mem hv₀_up) le_rfl
  calc ‖x t - x_c‖
      ≤ α₁.invFun (max S η) := (α₁.le_invFun_iff hxt_mem (max_rec' _ hS_mem hη_mem)).mpr h_α₁t
    _ = max (β.toFun ‖x t₀ - x_c‖ (t - t₀)) (α₁.invFun η) := by
        rw [α₁.invFun_max hS_mem hη_mem, hβ_eq]

/-- **Uniform boundedness from an ultimate bound certificate**: under the hypotheses of
`exists_classKL_ultimateBound_of_lyapunov`, the trajectories are uniformly bounded around `x_c`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18. -/
@[blueprint "cor:continuousSystem-uniformlyBounded-of-lyapunov"
  (title := "Uniform boundedness from a Lyapunov-like function")
  (latexEnv := "corollary")
  (statement := /-- Under the hypotheses of
    \cref{thm:continuousSystem-exists-classKL-ultimateBound-of-lyapunov}, the trajectories are
    uniformly bounded around $x_c$ (\cref{def:continuousSystem-uniformlyBounded}). -/)
  (proof := /-- The estimate of
    \cref{thm:continuousSystem-exists-classKL-ultimateBound-of-lyapunov}, and
    \cref{lem:continuousSystem-uniformlyBounded-of-classKL-bound}. -/)]
theorem uniformlyBounded_of_lyapunov [Nontrivial E] {s : ContinuousSystem E Unit Y}
    {V : ℝ → E → ℝ} {x_c : E} {r b₁ b₂ μ c : ℝ} (α₁ : ClassK r b₁) (α₂ : ClassK r b₂)
    {W₃ : E → ℝ} (hV : s.IsUltimateBoundLyapunovFunction V x_c α₁ α₂ W₃ μ)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c (closedBall x_c r))
    (hμ : 0 ≤ μ) (hμc : μ < c) (hcr : c < r) (hc : α₂.toFun c < b₁) :
    s.UniformlyBounded x_c := by
  obtain ⟨β, -, hβ⟩ :=
    exists_classKL_ultimateBound_of_lyapunov α₁ α₂ hW₃ (hμ.trans_lt hμc) hcr hc
  exact uniformlyBounded_of_classKL_bound β fun t₀ ht₀ t₁ x hx =>
    hβ hV hμ hμc t₀ ht₀ t₁ x (IsTrajectoryOn.isRightTrajectoryOn hx)

/-- **Uniform ultimate boundedness from an ultimate bound certificate**: under the hypotheses of
`exists_classKL_ultimateBound_of_lyapunov` with `μ > 0`, a forward-complete system is uniformly
ultimately bounded around `x_c` with ultimate bound `α₁⁻¹(α₂(μ))`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18. -/
@[blueprint "cor:continuousSystem-uniformlyUltimatelyBounded-of-lyapunov"
  (title := "Uniform ultimate boundedness from a Lyapunov-like function")
  (latexEnv := "corollary")
  (statement := /-- Under the hypotheses of
    \cref{thm:continuousSystem-exists-classKL-ultimateBound-of-lyapunov} with $\mu > 0$, if the
    system is forward complete from the $c$-ball about $x_c$ at every $t_0 \ge 0$
    (\cref{def:continuousSystem-isForwardCompleteOn}), its trajectories are uniformly
    ultimately bounded around $x_c$ with ultimate bound $\alpha_1^{-1}(\alpha_2(\mu))$
    (\cref{def:continuousSystem-uniformlyUltimatelyBounded}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.18, estimate (4.43). -/)
  (proof := /-- The estimate of
    \cref{thm:continuousSystem-exists-classKL-ultimateBound-of-lyapunov}, and
    \cref{lem:continuousSystem-uniformlyUltimatelyBounded-of-classKL-bound}
    with $b = \alpha_1^{-1}(\alpha_2(\mu)) > 0$. -/)]
theorem uniformlyUltimatelyBounded_of_lyapunov [Nontrivial E] {s : ContinuousSystem E Unit Y}
    {V : ℝ → E → ℝ} {x_c : E} {r b₁ b₂ μ c : ℝ} (α₁ : ClassK r b₁) (α₂ : ClassK r b₂)
    {W₃ : E → ℝ} (hV : s.IsUltimateBoundLyapunovFunction V x_c α₁ α₂ W₃ μ)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c (closedBall x_c r))
    (hμ : 0 < μ) (hμc : μ < c) (hcr : c < r) (hc : α₂.toFun c < b₁)
    (h_complete : ∀ t₀ : ℝ, 0 ≤ t₀ → s.IsForwardCompleteOn (fun _ => ()) t₀ (ball x_c c)) :
    s.UniformlyUltimatelyBounded x_c (α₁.invFun (α₂.toFun μ)) := by
  have hμ_mem : μ ∈ Ico 0 r := ⟨hμ.le, hμc.trans hcr⟩
  obtain ⟨β, -, hβ⟩ := exists_classKL_ultimateBound_of_lyapunov α₁ α₂ hW₃ (hμ.trans hμc) hcr hc
  -- The ultimate bound `α₁⁻¹(α₂(μ))` is positive.
  refine uniformlyUltimatelyBounded_of_classKL_bound β ((α₁.symm.pos_iff
    ⟨(α₂.maps_to hμ_mem).1, (α₂.strict_mono hμ_mem ⟨(hμ.trans hμc).le, hcr⟩ hμc).trans hc⟩).mpr
      ((α₂.pos_iff hμ_mem).mpr hμ)) h_complete fun t₀ ht₀ t₁ x hx =>
    hβ hV hμ.le hμc t₀ ht₀ t₁ x (IsTrajectoryOn.isRightTrajectoryOn hx)

/-! ## The global case -/

/-- **Khalil's ultimate boundedness theorem, global case.**  If `V` is a global ultimate bound
Lyapunov function, then every trajectory obeys
`‖x(t) - x_c‖ ≤ max (β(‖x(t₀) - x_c‖, t - t₀)) (α₁⁻¹(α₂(μ)))` for a single global class `KL`
function `β`.

`W₃` need not be bounded below away from the origin: a positive definite `W₃` may tend to `0` at
infinity, so no class `K` function of `‖x - x_c‖` lies below it on all of `E`, and the class
`KL` bound of each ball cannot simply be reused for every ball.  Instead the local bounds of the
balls of radius `k + 1`, `k ∈ ℕ`, are summed into a family of decay envelopes monotone in the
radius, which `ClassKLGlobal.exists_ge_min_of_decay` assembles into one global class `KL`
function.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18, global case. -/
@[blueprint "thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov"
  (title := "Ultimate boundedness theorem, global case")
  (statement := /-- Let the state space be $\mathbb{R}^n$, $V$ a global ultimate bound Lyapunov
    function about $x_c$ with data $\alpha_1, \alpha_2, W_3, \mu$
    (\cref{def:continuousSystem-isGlobalUltimateBoundLyapunovFunction}), $W_3$ positive
    definite about $x_c$ on $\mathbb{R}^n$ (\cref{def:isPositiveDefiniteOn}) and
    $\mu \ge 0$.  Then there is a global class $\mathcal{KL}$
    function $\beta$ (\cref{def:isClassKLGlobal}), depending only on $\alpha_1, \alpha_2$ and
    $W_3$ --- not on the system, $V$ or $\mu$ --- such that every right trajectory
    (\cref{def:continuousSystem-isRightTrajectoryOn}) on a segment $[t_0, t_1]$, $t_0 \ge 0$,
    satisfies
    \[
      \|x(t) - x_c\| \le \max\bigl\{\beta(\|x(t_0) - x_c\|, t - t_0),\;
        \alpha_1^{-1}(\alpha_2(\mu))\bigr\} \qquad \forall\, t \in [t_0, t_1].
    \]

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.18, global case.
    Khalil's proof chooses one class $\mathcal{K}$ lower bound for $W_3$ on all of
    $\mathbb{R}^n$, which need not exist: $W_3$ may tend to $0$ at infinity. -/)
  (proof := /-- For each $k \in \mathbb{N}$, apply
    \cref{thm:continuousSystem-exists-classKL-ultimateBound-of-lyapunov} with initial radius
    $c_k = k + 1$, on a ball large enough that $\alpha_2(c_k) < \alpha_1(R_k)$.  If
    $\mu \ge \|x(t_0) - x_c\|$, the bound of $\beta_k$ at an index with $c_k > \mu$ is at most
    $\alpha_1^{-1}(\alpha_2(\mu))$, so the trajectory never leaves the ultimate bound.  It gives a
    class $\mathcal{KL}$ $\beta_k$ with $\beta_k(\rho, s) \le \alpha_1^{-1}(\alpha_2(\rho))$.  The
    sums $U(r, s) = \sum_{k \le \lceil r \rceil} \beta_k(k, s)$ are positive, decreasing to $0$
    in $s$, and increasing in $r$, and a trajectory from the $r$-ball that is outside the
    ultimate bound at time $t$ is within $\beta_{\lceil r \rceil}(r, t - t_0) \le U(r + 1, t - t_0)$
    and within $\alpha(r) = \alpha_1^{-1}(\alpha_2(r))$ of $x_c$.
    \cref{lem:classKLGlobal-exists-ge-min-of-decay} turns the class $\mathcal{K}_{\infty}$
    bound $\alpha$ and the family $U$ into a global class $\mathcal{KL}$ $\beta$ above
    $\min\{\alpha(r), U(r + 1, s)\}$. -/)]
theorem exists_classKLGlobal_ultimateBound_of_lyapunov [Nontrivial E] {x_c : E}
    (α₁ α₂ : ClassKInfty) {W₃ : E → ℝ} (hW₃ : IsPositiveDefiniteOn W₃ x_c univ) :
    ∃ β : ClassKLGlobal,
      ∀ {Y : Type u} {s : ContinuousSystem E Unit Y} {V : ℝ → E → ℝ} {μ : ℝ},
        s.IsGlobalUltimateBoundLyapunovFunction V x_c α₁ α₂ W₃ μ → 0 ≤ μ →
        ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
          s.IsRightTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
            ∀ t ∈ Icc t₀ t₁,
              ‖x t - x_c‖ ≤ max (β.toFun ‖x t₀ - x_c‖ (t - t₀)) (α₁.invFun (α₂.toFun μ)) := by
  -- Step 1. The local theorem from the ball of radius `k + 1`, for each `k : ℕ`, read through the
  -- class `K∞` functions.
  have h_local : ∀ k : ℕ, ∃ β : ClassKL (k + 1),
      (∀ ρ ∈ Ico 0 ((k : ℝ) + 1), ∀ θ : ℝ, 0 ≤ θ → β.toFun ρ θ ≤ α₁.invFun (α₂.toFun ρ)) ∧
      ∀ {Y : Type u} {s : ContinuousSystem E Unit Y} {V : ℝ → E → ℝ} {μ : ℝ},
        s.IsGlobalUltimateBoundLyapunovFunction V x_c α₁ α₂ W₃ μ → 0 ≤ μ → μ < k + 1 →
        ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
          s.IsRightTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_c‖ < k + 1 →
            ∀ t ∈ Icc t₀ t₁,
              ‖x t - x_c‖ ≤ max (β.toFun ‖x t₀ - x_c‖ (t - t₀)) (α₁.invFun (α₂.toFun μ)) := by
    intro k
    set c : ℝ := k + 1
    have hc_pos : 0 < c := by positivity
    -- A radius `R > c` large enough that `α₂(c) < α₁(R)`.
    set R := max (c + 1) (α₁.invFun (α₂.toFun c) + 1)
    have hcR : c < R := (lt_add_one c).trans_le (le_max_left _ _)
    have hR_pos : 0 < R := hc_pos.trans hcR
    have hα₂c_mem : α₂.toFun c ∈ Ici 0 := α₂.maps_to hc_pos.le
    have h_α₂c : α₂.toFun c < α₁.toFun R := by
      calc α₂.toFun c
          = α₁.toFun (α₁.invFun (α₂.toFun c)) := (α₁.right_inv hα₂c_mem).symm
        _ < α₁.toFun R := α₁.strict_mono (α₁.inv_maps_to hα₂c_mem) hR_pos.le
            ((lt_add_one _).trans_le (le_max_right _ _))
    obtain ⟨β, hβ_le, hβ⟩ := exists_classKL_ultimateBound_of_lyapunov
      (α₁.toClassK hR_pos) (α₂.toClassK hR_pos) (hW₃.mono (subset_univ _)) hc_pos hcR h_α₂c
    -- The restrictions keep the inverse of `α₁` on the values `α₂` takes below `c`.
    have h_inv : ∀ ρ ∈ Icc 0 c,
        (α₁.toClassK hR_pos).invFun (α₂.toFun ρ) = α₁.invFun (α₂.toFun ρ) := fun ρ hρ =>
      α₁.toClassK_invFun hR_pos
        ⟨α₂.maps_to hρ.1, (α₂.strict_mono.monotoneOn hρ.1 hc_pos.le hρ.2).trans_lt h_α₂c⟩
    refine ⟨β, fun ρ hρ θ hθ => ?_,
      fun {Y s V μ} hV hμ hμc t₀ ht₀ t₁ x hx h_init t ht => ?_⟩
    · have h : β.toFun ρ θ ≤ (α₁.toClassK hR_pos).invFun (α₂.toFun ρ) := hβ_le ρ hρ θ hθ
      rwa [h_inv ρ (Ico_subset_Icc_self hρ)] at h
    · have h : ‖x t - x_c‖ ≤ max (β.toFun ‖x t₀ - x_c‖ (t - t₀))
          ((α₁.toClassK hR_pos).invFun (α₂.toFun μ)) :=
        hβ ⟨fun t ht y _ => hV.differentiableAt t ht y, fun t ht y _ => hV.sandwich t ht y,
          fun t ht y hy _ => hV.decrease t ht y hy⟩ hμ hμc
          t₀ ht₀ t₁ x hx h_init t ht
      rwa [h_inv μ ⟨hμ, hμc.le⟩] at h
  choose β hβ_le hβ using h_local
  -- Step 2. The decay envelopes `U(r, θ) = ∑_{k ≤ ⌈r⌉} βₖ(k, θ)`: more terms for a larger radius.
  let U : ℝ → ℝ → ℝ := fun r θ => ∑ k ∈ Finset.range (⌈r⌉₊ + 1), (β k).toFun k θ
  have hk_mem : ∀ k : ℕ, (k : ℝ) ∈ Ico 0 ((k : ℝ) + 1) := fun k =>
    ⟨k.cast_nonneg, lt_add_one _⟩
  have h_term_nonneg : ∀ k : ℕ, ∀ θ : ℝ, 0 ≤ θ → 0 ≤ (β k).toFun k θ := fun k θ hθ =>
    (β k).nonneg _ (hk_mem k) θ hθ
  have hU_pos : ∀ r > 0, ∀ θ > 0, 0 < U r θ := by
    intro r hr θ hθ
    have h_mono : (β ⌈r⌉₊).toFun 0 θ < (β ⌈r⌉₊).toFun ⌈r⌉₊ θ :=
      (β ⌈r⌉₊).strict_mono_r θ hθ.le ⟨le_rfl, by positivity⟩ (hk_mem _)
        (Nat.cast_pos.mpr (Nat.ceil_pos.mpr hr))
    rw [(β ⌈r⌉₊).map_zero_r hθ.le] at h_mono
    exact h_mono.trans_le (Finset.single_le_sum (fun k _ => h_term_nonneg k θ hθ.le)
      (Finset.self_mem_range_succ _))
  have hU_anti : ∀ r > 0, AntitoneOn (U r) (Ioi 0) := fun r _ θ₁ hθ₁ θ₂ hθ₂ hθ =>
    Finset.sum_le_sum fun k _ => (β k).anti_s _ (hk_mem k) (mem_Ici.mpr (mem_Ioi.mp hθ₁).le)
      (mem_Ici.mpr (mem_Ioi.mp hθ₂).le) hθ
  have hU_tendsto : ∀ r > 0, Tendsto (U r) atTop (𝓝 0) := fun r _ => by
    simpa using tendsto_finset_sum (Finset.range (⌈r⌉₊ + 1))
      fun k _ => (β k).tendsto_zero _ (hk_mem k)
  have hU_mono : ∀ θ > 0, MonotoneOn (fun r => U (r + 1) θ) (Ici 0) :=
    fun θ hθ r₁ _ r₂ _ hr => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.add_le_add_right (Nat.ceil_mono (by linarith)) 1))
      fun k _ _ => h_term_nonneg k θ hθ.le
  -- Step 3. The class `K∞` bound `α = α₁⁻¹ ∘ α₂`, and the global class KL function.
  let α : ClassKInfty := α₁.symm.comp α₂
  obtain ⟨B, hB_zero, hB_pos⟩ :=
    ClassKLGlobal.exists_ge_min_of_decay α U hU_pos hU_anti hU_tendsto hU_mono
  refine ⟨B, fun {Y s V μ} hV hμ t₀ ht₀ t₁ x hx t ht => ?_⟩
  set r₀ := ‖x t₀ - x_c‖
  set b := α₁.invFun (α₂.toFun μ)
  rcases le_or_gt ‖x t - x_c‖ b with h_in | h_out
  · exact le_max_of_le_right h_in
  refine le_max_of_le_left ?_
  have hθ : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
  -- Step 4. From the ball of radius `j + 1 > max r₀ μ`, `‖x(t) - x_c‖ ≤ βⱼ(r₀, θ) ≤ α(r₀)`, as
  -- the trajectory is outside the ultimate bound.
  have h_bound : ∀ j : ℕ, r₀ < j + 1 → μ < j + 1 → ‖x t - x_c‖ ≤ (β j).toFun r₀ (t - t₀) ∧
      ‖x t - x_c‖ ≤ α.toFun r₀ := fun j hr₀j hμj => by
    have h := (le_max_iff.mp (hβ j hV hμ hμj t₀ ht₀ t₁ x hx hr₀j t ht)).resolve_right
      h_out.not_ge
    exact ⟨h, h.trans (hβ_le j r₀ ⟨norm_nonneg _, hr₀j⟩ _ hθ)⟩
  -- If `μ ≥ r₀`, that bound is itself at most `α(μ) = b`: the trajectory never left `b`.
  rcases le_or_gt μ r₀ with hμr₀ | hr₀μ
  swap
  · have h := (h_bound ⌈μ⌉₊ (hr₀μ.trans_le (Nat.le_ceil μ) |>.trans (lt_add_one _))
      ((Nat.le_ceil μ).trans_lt (lt_add_one _))).2
    exact absurd (h.trans (α.strict_mono.monotoneOn (norm_nonneg _) hμ hr₀μ.le)) h_out.not_ge
  -- Otherwise use `k = ⌈r₀⌉`: `βₖ(r₀, θ) ≤ βₖ(k, θ) ≤ U(r₀ + 1, θ)`.
  set k := ⌈r₀⌉₊
  have hr₀_le : r₀ ≤ k := Nat.le_ceil r₀
  have hr₀_mem : r₀ ∈ Ico 0 ((k : ℝ) + 1) := ⟨norm_nonneg _, hr₀_le.trans_lt (lt_add_one _)⟩
  obtain ⟨h_β, h_α⟩ := h_bound k hr₀_mem.2 (hμr₀.trans_lt hr₀_mem.2)
  have h_U : ‖x t - x_c‖ ≤ U (r₀ + 1) (t - t₀) :=
    h_β.trans (((β k).mono_r hr₀_mem (hk_mem k) hθ hr₀_le).trans
      (Finset.single_le_sum (fun j _ => h_term_nonneg j _ hθ)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono (by linarith))))))
  rcases hθ.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact h_α.trans (hB_zero r₀ (norm_nonneg _))
  · exact (le_min h_α h_U).trans (hB_pos r₀ (norm_nonneg _) _ hpos)

/-- **Global uniform boundedness from an ultimate bound certificate**: under the hypotheses of
`exists_classKLGlobal_ultimateBound_of_lyapunov`, the trajectories are globally uniformly
bounded around `x_c`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18, global case. -/
@[blueprint "cor:continuousSystem-globallyUniformlyBounded-of-lyapunov"
  (title := "Global uniform boundedness from a Lyapunov-like function")
  (latexEnv := "corollary")
  (statement := /-- Under the hypotheses of
    \cref{thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov}, the trajectories
    are globally uniformly bounded around $x_c$
    (\cref{def:continuousSystem-globallyUniformlyBounded}). -/)
  (proof := /-- The estimate of
    \cref{thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov}, and
    \cref{lem:continuousSystem-globallyUniformlyBounded-of-classKL-bound}. -/)]
theorem globallyUniformlyBounded_of_lyapunov [Nontrivial E] {s : ContinuousSystem E Unit Y}
    {V : ℝ → E → ℝ} {x_c : E} {μ : ℝ} (α₁ α₂ : ClassKInfty) {W₃ : E → ℝ}
    (hV : s.IsGlobalUltimateBoundLyapunovFunction V x_c α₁ α₂ W₃ μ)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c univ)
    (hμ : 0 ≤ μ) :
    s.GloballyUniformlyBounded x_c := by
  obtain ⟨β, hβ⟩ := exists_classKLGlobal_ultimateBound_of_lyapunov α₁ α₂ hW₃
  exact globallyUniformlyBounded_of_classKL_bound β fun t₀ ht₀ t₁ x hx =>
    hβ hV hμ t₀ ht₀ t₁ x (IsTrajectoryOn.isRightTrajectoryOn hx)

/-- **Global uniform ultimate boundedness from an ultimate bound certificate**: under the
hypotheses of `exists_classKLGlobal_ultimateBound_of_lyapunov` with `μ > 0`, a forward-complete
system is globally uniformly ultimately bounded around `x_c` with ultimate bound `α₁⁻¹(α₂(μ))`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.18, global case. -/
@[blueprint "cor:continuousSystem-globallyUniformlyUltimatelyBounded-of-lyapunov"
  (title := "Global uniform ultimate boundedness from a Lyapunov-like function")
  (latexEnv := "corollary")
  (statement := /-- Under the hypotheses of
    \cref{thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov} with $\mu > 0$,
    if the system is forward complete from every state at every $t_0 \ge 0$
    (\cref{def:continuousSystem-isForwardCompleteOn}), its trajectories are globally uniformly
    ultimately bounded around $x_c$ with ultimate bound $\alpha_1^{-1}(\alpha_2(\mu))$
    (\cref{def:continuousSystem-globallyUniformlyUltimatelyBounded}). -/)
  (proof := /-- The estimate of
    \cref{thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov}, and
    \cref{lem:continuousSystem-globallyUniformlyUltimatelyBounded-of-classKL-bound}
    with $b = \alpha_1^{-1}(\alpha_2(\mu)) > 0$. -/)]
theorem globallyUniformlyUltimatelyBounded_of_lyapunov [Nontrivial E]
    {s : ContinuousSystem E Unit Y} {V : ℝ → E → ℝ} {x_c : E} {μ : ℝ}
    (α₁ α₂ : ClassKInfty) {W₃ : E → ℝ}
    (hV : s.IsGlobalUltimateBoundLyapunovFunction V x_c α₁ α₂ W₃ μ)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c univ)
    (hμ : 0 < μ) (h_complete : ∀ t₀ : ℝ, 0 ≤ t₀ → s.IsForwardCompleteOn (fun _ => ()) t₀ univ) :
    s.GloballyUniformlyUltimatelyBounded x_c (α₁.invFun (α₂.toFun μ)) := by
  obtain ⟨β, hβ⟩ := exists_classKLGlobal_ultimateBound_of_lyapunov α₁ α₂ hW₃
  -- The ultimate bound `α₁⁻¹(α₂(μ))` is positive.
  exact globallyUniformlyUltimatelyBounded_of_classKL_bound β
    ((α₁.symm.pos_iff (α₂.maps_to hμ.le)).mpr ((α₂.pos_iff hμ.le).mpr hμ)) h_complete
    fun t₀ ht₀ t₁ x hx => hβ hV hμ.le t₀ ht₀ t₁ x (IsTrajectoryOn.isRightTrajectoryOn hx)

end ContinuousSystem
