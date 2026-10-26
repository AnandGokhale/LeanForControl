import LeanForControl.Stability.Continuous.Boundedness
import LeanForControl.Stability.Continuous.Converse
import Architect

/-!
# `Stability.Continuous.ISS` — input-to-state stability

A system with input is *input-to-state stable* about `(x_eq, u_eq)` when every trajectory obeys
`‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t - t₀) + γ(M)` for any bound `M` on `‖u - u_eq‖` over
`[t₀, t]`: the effect of the initial state decays, and the input contributes at most a gain of
its distance from `u_eq`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.9, Definition 4.7 and Theorem 4.19;
Sontag, *Input to state stability: basic concepts and results*, in *Nonlinear and Optimal Control
Theory*, Lecture Notes in Mathematics 1932, Springer (2008).

## Main results

* `InputToStateStable` — Khalil's Definition 4.7, with a class `K∞` gain.
* `norm_le_of_isISSLyapunov` — the estimate of Khalil's Theorem 4.19, for a merely monotone `ρ`:
  `‖x(t) - x_c‖ ≤ β(‖x(t₀) - x_c‖, t - t₀) + α₁⁻¹(α₂(ρ(M)))`.
* `inputToStateStable_of_isISSLyapunov` — Theorem 4.19 itself, with `ρ` of class `K∞`.
* `inputToStateStable_of_globallyExponentiallyStable` — Khalil's Lemma 4.6: a system whose
  unforced part is globally exponentially stable, and whose field is Lipschitz in the input, is
  input-to-state stable.
* `InputToStateStable.globallyUniformlyAsymptoticallyStable` — with the input held at `u_eq`,
  an input-to-state stable system is globally uniformly asymptotically stable.

## The argument

Fix an input `u` and a time `t`, and freeze `u` into the system: `ẋ = F(τ, x, u(τ))` is an
unforced time-varying system.  Clamping `u` to `[t₀, t]` keeps the decrease condition
`V̇ ≤ -W₃(x)` for `‖x - x_c‖ ≥ ρ(M)` at every time.  The global ultimate boundedness theorem then
applies with `μ = ρ(M)`, and its class `KL` function `β` depends neither on the system nor on `μ`,
so the same `β` serves every input.

## Differences from Khalil

* The equilibrium and the input are measured from a general `(x_eq, u_eq)`; Khalil places both at
  the origin.  This is what a cascade needs: the driving state converges to its equilibrium, not
  to `0`.
* The input enters through any bound `M` on `‖u - u_eq‖` over `[t₀, t]` rather than its
  supremum; the
  two are equivalent, taking `M` to be the supremum, and a bound avoids the junk value of `sSup`
  on an unbounded set.
* The gain `γ` is class `K∞` rather than class `K`, as in Sontag.  Nothing is lost: a class `K`
  gain `γ` is dominated by `γ + id`, of class `K∞`.  Theorem 4.19 accordingly asks for `ρ` of
  class `K∞`, also no loss, since enlarging `ρ` only weakens its hypothesis;
  `norm_le_of_isISSLyapunov` keeps Khalil's exact gain `α₁⁻¹ ∘ α₂ ∘ ρ` for any monotone `ρ`.
* Trajectories are *right trajectories* (`IsRightTrajectoryOn`): continuous, with right
  derivative `F(t, x, u(t))`.  These are the solutions under piecewise continuous inputs, taken
  right-continuous — Khalil's input class — so the estimate covers step, sample-and-hold and
  switching inputs, whose solutions have corners.  Every classical trajectory is one.
* As for every bound in this library, trajectories are quantified on segments: solutions are not
  required to exist for all time (see the forward-completeness item in `Stability/plan.md`).
-/

open Set Filter Topology Metric

namespace ContinuousSystem

variable {E U Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup U]

/-- The system is **input-to-state stable** about `(x_eq, u_eq)`: there are a global class `KL`
function `β` and a class `K∞` gain `γ` with `‖x(t) - x_eq‖ ≤ β(‖x(t₀) - x_eq‖, t - t₀) + γ(M)`
along every right trajectory, whenever `M` bounds `‖u - u_eq‖` on `[t₀, t]`.  Right trajectories
are the solutions under piecewise continuous, right-continuous inputs, so discontinuous inputs are
covered.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.7; Sontag (2008), for the class
`K∞` gain. -/
@[blueprint "def:continuousSystem-inputToStateStable"
  (title := "Input-to-state stability")
  (statement := /-- A continuous-time system with input is \emph{input-to-state stable} about
    $(x_{\mathrm{eq}}, u_{\mathrm{eq}})$ when there are a global class $\mathcal{KL}$ function
    $\beta$
    (\cref{def:isClassKLGlobal}) and a class $\mathcal{K}_{\infty}$ function $\gamma$
    (\cref{def:isClassKInfty}) such that every right trajectory
    (\cref{def:continuousSystem-isRightTrajectoryOn}) on a segment $[t_0, t_1]$, $t_0 \ge 0$,
    under any input $u$ satisfies
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0) + \gamma(M)
      \qquad \forall\, t \in [t_0, t_1]
    \]
    whenever $\|u(\tau) - u_{\mathrm{eq}}\| \le M$ for all $\tau \in [t_0, t]$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.7.  Differences:
    \begin{itemize} \item The equilibrium and the input are measured from a general
    $(x_{\mathrm{eq}}, u_{\mathrm{eq}})$ rather than the origin.  \item Any bound $M$ on the
    input replaces its supremum, which is equivalent.
    \item $\gamma$ is class $\mathcal{K}_{\infty}$, as in Sontag, rather than class
    $\mathcal{K}$; a class $\mathcal{K}$ gain $\gamma$ is dominated by $\gamma + \mathrm{id}$.
    \item Trajectories are right trajectories, the solutions under Khalil's piecewise continuous
    inputs (taken right-continuous): continuous, with right derivative $F(t, x, u(t))$.
    \item Solutions are not required to exist for all time. \end{itemize} -/)]
def InputToStateStable (s : ContinuousSystem E U Y) (x_eq : E) (u_eq : U) : Prop :=
  ∃ β : ClassKLGlobal, ∃ γ : ClassKInfty, ∀ t₀ : ℝ, 0 ≤ t₀ →
    ∀ (t₁ : ℝ) (u : ℝ → U) (x : ℝ → E), s.IsRightTrajectoryOn u x (Icc t₀ t₁) →
      ∀ t ∈ Icc t₀ t₁, ∀ M : ℝ, (∀ τ ∈ Icc t₀ t, ‖u τ - u_eq‖ ≤ M) →
        ‖x t - x_eq‖ ≤ β.toFun ‖x t₀ - x_eq‖ (t - t₀) + γ.toFun M

/-- **Input-to-state stability implies global uniform asymptotic stability with the input held
at `u_eq`**: with `u ≡ u_eq` and `M = 0` the estimate is a global class `KL` bound.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.9, after Definition 4.7. -/
@[blueprint "thm:continuousSystem-inputToStateStable-globallyUniformlyAsymptoticallyStable"
  (title := "Input-to-state stability implies global uniform asymptotic stability")
  (statement := /-- If $s$ is input-to-state stable about $x_{\mathrm{eq}}$
    (\cref{def:continuousSystem-inputToStateStable}), then $x_{\mathrm{eq}}$ is a globally
    uniformly asymptotically stable equilibrium of the system with the input held at
    $u_{\mathrm{eq}}$, $\dot x = F(t, x, u_{\mathrm{eq}})$
    (\cref{def:continuousSystem-constInput},
    \cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 4.9. -/)
  (proof := /-- With $u \equiv u_{\mathrm{eq}}$ and $M = 0$, $\gamma(M) = 0$ and the estimate is
    $\|x(t) - x_{\mathrm{eq}}\| \le \beta(\|x(t_0) - x_{\mathrm{eq}}\|, t - t_0)$, a global
    class $\mathcal{KL}$ bound;
    \cref{lem:continuousSystem-globallyUniformlyAsymptoticallyStable-iff-classKL} concludes. -/)]
theorem InputToStateStable.globallyUniformlyAsymptoticallyStable {s : ContinuousSystem E U Y}
    {x_eq : E} {u_eq : U} (h : s.InputToStateStable x_eq u_eq) :
    (s.constInput u_eq).GloballyUniformlyAsymptoticallyStable x_eq := by
  obtain ⟨β, γ, hβ⟩ := h
  -- With `u ≡ u_eq` and `M = 0`, `γ(M) = 0` and the estimate is a global class `KL` bound.
  refine (globallyUniformlyAsymptoticallyStable_iff_classKL _ _).mpr
    ⟨β, fun t₀ ht₀ t₁ x hx t ht => ?_⟩
  have h := hβ t₀ ht₀ t₁ (fun _ => u_eq) x (IsTrajectoryOn.isRightTrajectoryOn hx) t ht 0
    fun _ _ => by simp
  rwa [γ.map_zero, add_zero] at h

section ISSLyapunov

universe u

variable {U' Y' : Type u} [NormedAddCommGroup U'] [FiniteDimensional ℝ E]

/-- **The input-to-state estimate of an ISS-Lyapunov function.**  Let
`α₁(‖x - x_c‖) ≤ V(t, x) ≤ α₂(‖x - x_c‖)` with `α₁, α₂` of class `K∞`, and `V̇ ≤ -W₃(x)`
whenever `‖x - x_c‖ ≥ ρ(‖u - u_eq‖)`, with `W₃` positive definite and `ρ` nonnegative and
monotone.  Then `‖x(t) - x_c‖ ≤ β(‖x(t₀) - x_c‖, t - t₀) + α₁⁻¹(α₂(ρ(M)))` whenever `M` bounds
`‖u - u_eq‖` on
`[t₀, t]`, for a single global class `KL` function `β`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.19 and its proof. -/
@[blueprint "thm:continuousSystem-norm-le-of-isISSLyapunov"
  (title := "Input-to-state estimate from an ISS-Lyapunov function")
  (statement := /-- Let the state space be $\mathbb{R}^n$, $V$ differentiable at every $(t, x)$
    with $t \ge 0$, $\alpha_1,
    \alpha_2$ class $\mathcal{K}_{\infty}$, $W_3$ positive definite about $x_c$ on
    $\mathbb{R}^n$ (\cref{def:isPositiveDefiniteOn}), and $\rho : [0, \infty) \to [0, \infty)$
    nondecreasing, with
    \[
      \alpha_1(\|x - x_c\|) \le V(t, x) \le \alpha_2(\|x - x_c\|), \qquad
      \dot V(t, x, u) \le -W_3(x) \quad
        \text{for } \|x - x_c\| \ge \rho(\|u - u_{\mathrm{eq}}\|)
    \]
    for all $t \ge 0$, $x$ and $u$.  Then there is a global class $\mathcal{KL}$ function
    $\beta$ such that every right trajectory
    (\cref{def:continuousSystem-isRightTrajectoryOn}) on a segment $[t_0, t_1]$, $t_0 \ge 0$,
    satisfies
    \[
      \|x(t) - x_c\| \le \beta(\|x(t_0) - x_c\|, t - t_0) + \alpha_1^{-1}(\alpha_2(\rho(M)))
    \]
    for $t \in [t_0, t_1]$, whenever $\|u(\tau) - u_{\mathrm{eq}}\| \le M$ for all
    $\tau \in [t_0, t]$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.19, with
    $u_{\mathrm{eq}} = 0$ and $\rho$ class $\mathcal{K}$; only its monotonicity is used. -/)
  (proof := /-- Fix the input and $t$.  Freeze the input, clamped to $[t_0, t]$, into the
    system: $\dot x = F(\tau, x, u(\tau))$ is an unforced system with the same trajectories on
    $[t_0, t]$, and since $\|u(\tau) - u_{\mathrm{eq}}\| \le M$ and $\rho$ is nondecreasing,
    $\dot V \le -W_3$ wherever $\|x - x_c\| \ge \rho(M)$.  Apply
    \cref{thm:continuousSystem-exists-classKLGlobal-ultimateBound-of-lyapunov} with
    $\mu = \rho(M)$; its $\beta$ does not depend on the system or on $\mu$, so it is the same for
    every input.  Finally $\max\{a, b\} \le a + b$ for $a, b \ge 0$. -/)]
theorem norm_le_of_isISSLyapunov [Nontrivial E] {s : ContinuousSystem E U' Y'}
    {V : ℝ → E → ℝ} {x_c : E} {u_eq : U'} (α₁ α₂ : ClassKInfty) {W₃ : E → ℝ} {ρ : ℝ → ℝ}
    (hV : ∀ t : ℝ, 0 ≤ t → ∀ y : E, DifferentiableAt ℝ (Function.uncurry V) (t, y))
    (hV_bd : ∀ t : ℝ, 0 ≤ t → ∀ y : E,
      α₁.toFun ‖y - x_c‖ ≤ V t y ∧ V t y ≤ α₂.toFun ‖y - x_c‖)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c univ)
    (hρ_mono : MonotoneOn ρ (Ici 0)) (hρ_nonneg : ∀ r, 0 ≤ r → 0 ≤ ρ r)
    (hlie : ∀ t : ℝ, 0 ≤ t → ∀ (y : E) (w : U'), ρ ‖w - u_eq‖ ≤ ‖y - x_c‖ →
      s.lieDerivative V t y w ≤ -W₃ y) :
    ∃ β : ClassKLGlobal, ∀ t₀ : ℝ, 0 ≤ t₀ →
      ∀ (t₁ : ℝ) (u : ℝ → U') (x : ℝ → E), s.IsRightTrajectoryOn u x (Icc t₀ t₁) →
        ∀ t ∈ Icc t₀ t₁, ∀ M : ℝ, (∀ τ ∈ Icc t₀ t, ‖u τ - u_eq‖ ≤ M) →
          ‖x t - x_c‖ ≤ β.toFun ‖x t₀ - x_c‖ (t - t₀) + α₁.invFun (α₂.toFun (ρ M)) := by
  -- `β` is chosen once, before the input.
  obtain ⟨β, hβ⟩ := exists_classKLGlobal_ultimateBound_of_lyapunov.{u} α₁ α₂ hW₃
  refine ⟨β, fun t₀ ht₀ t₁ u x hx t ht M hM => ?_⟩
  have hM_nonneg : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, ht.1⟩)
  -- Step 1. Freeze the input, clamped to `[t₀, t]`, into an unforced system.
  let clamp : ℝ → ℝ := fun τ => max t₀ (min τ t)
  have h_clamp_mem : ∀ τ, clamp τ ∈ Icc t₀ t := fun τ =>
    ⟨le_max_left _ _, max_le ht.1 (min_le_right _ _)⟩
  have h_clamp_eq : ∀ τ ∈ Icc t₀ t, clamp τ = τ := fun τ hτ => by
    simp only [clamp, min_eq_left hτ.2, max_eq_right hτ.1]
  let s' : ContinuousSystem E Unit Y' :=
    autonomous (fun τ y => s.F τ y (u (clamp τ))) (fun τ y => s.h τ y (u (clamp τ)))
  -- On `[t₀, t]` the frozen system has the same trajectories ...
  have hx' : s'.IsRightTrajectoryOn (fun _ => ()) x (Icc t₀ t) :=
    ⟨hx.1.mono (Icc_subset_Icc_right ht.2), fun τ hτ => by
      simpa [s', vectorField, h_clamp_eq τ hτ] using (hx.2 τ ⟨hτ.1, hτ.2.trans ht.2⟩).mono
        (inter_subset_inter_left _ (Icc_subset_Icc_right ht.2))⟩
  -- ... and `V̇ ≤ -W₃` outside the ball of radius `ρ(M)`, as `ρ(‖u - u_eq‖) ≤ ρ(M)` at every
  -- time.
  have hlie' : ∀ τ : ℝ, 0 ≤ τ → ∀ y : E, ρ M ≤ ‖y - x_c‖ →
      s'.lieDerivative V τ y () ≤ -W₃ y := fun τ hτ y hy =>
    hlie τ hτ y (u (clamp τ)) ((hρ_mono (norm_nonneg _) hM_nonneg
      (hM _ (h_clamp_mem τ))).trans hy)
  -- Step 2. The global ultimate bound with `μ = ρ(M)`, and `max ≤ sum`.
  have h := hβ hV hV_bd hlie' (hρ_nonneg M hM_nonneg) t₀ ht₀ t x hx' t ⟨ht.1, le_rfl⟩
  exact h.trans (max_le_add_of_nonneg (β.nonneg _ (norm_nonneg _) _ (sub_nonneg.mpr ht.1))
    (α₁.inv_maps_to (α₂.maps_to (hρ_nonneg M hM_nonneg))))

/-- **ISS-Lyapunov functions certify input-to-state stability**, with gain
`γ = α₁⁻¹ ∘ α₂ ∘ ρ`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.19. -/
@[blueprint "thm:continuousSystem-inputToStateStable-of-isISSLyapunov"
  (title := "ISS-Lyapunov theorem")
  (statement := /-- Under the hypotheses of \cref{thm:continuousSystem-norm-le-of-isISSLyapunov}
    with $\rho$ class $\mathcal{K}_{\infty}$, the system is input-to-state stable about
    $(x_c, u_{\mathrm{eq}})$
    (\cref{def:continuousSystem-inputToStateStable}) with gain
    $\gamma = \alpha_1^{-1} \circ \alpha_2 \circ \rho$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.19, with $\rho$ of class
    $\mathcal{K}$; a class $\mathcal{K}$ $\rho$ can be replaced by $\rho + \mathrm{id}$, which
    only weakens the hypothesis. -/)
  (proof := /-- \cref{thm:continuousSystem-norm-le-of-isISSLyapunov}, with
    $\alpha_1^{-1} \circ \alpha_2 \circ \rho$ class $\mathcal{K}_{\infty}$
    (\cref{lem:classKInfty-symm}, \cref{lem:classKInfty-comp}). -/)]
theorem inputToStateStable_of_isISSLyapunov [Nontrivial E] {s : ContinuousSystem E U' Y'}
    {V : ℝ → E → ℝ} {x_c : E} {u_eq : U'} (α₁ α₂ ρ : ClassKInfty) {W₃ : E → ℝ}
    (hV : ∀ t : ℝ, 0 ≤ t → ∀ y : E, DifferentiableAt ℝ (Function.uncurry V) (t, y))
    (hV_bd : ∀ t : ℝ, 0 ≤ t → ∀ y : E,
      α₁.toFun ‖y - x_c‖ ≤ V t y ∧ V t y ≤ α₂.toFun ‖y - x_c‖)
    (hW₃ : IsPositiveDefiniteOn W₃ x_c univ)
    (hlie : ∀ t : ℝ, 0 ≤ t → ∀ (y : E) (w : U'), ρ.toFun ‖w - u_eq‖ ≤ ‖y - x_c‖ →
      s.lieDerivative V t y w ≤ -W₃ y) :
    s.InputToStateStable x_c u_eq := by
  obtain ⟨β, hβ⟩ := norm_le_of_isISSLyapunov α₁ α₂ hV hV_bd hW₃ ρ.strict_mono.monotoneOn
    (fun r hr => ρ.maps_to hr) hlie
  exact ⟨β, α₁.symm.comp (α₂.comp ρ), hβ⟩

/-- **Global exponential stability of the unforced system gives input-to-state stability.**
Let the field with the input held at `u_eq`, `f(t, x, u_eq)`, be continuously differentiable and
globally Lipschitz in `x`, uniformly in `t`, and let the input enter Lipschitz:
`‖f(t, x, u) - f(t, x, u_eq)‖ ≤ L ‖u - u_eq‖`.  If `x_c` is a globally exponentially stable
equilibrium of `ẋ = f(t, x, u_eq)`, the system is input-to-state stable about `(x_c, u_eq)`.

The converse Lyapunov function `V` of `ẋ = f(t, x, u_eq)` (Theorem 4.14) is an ISS-Lyapunov
function: along the forced system `V̇ ≤ -c₃‖x - x_c‖² + c₄ L ‖x - x_c‖ ‖u - u_eq‖`, which is at
most `-(c₃/2)‖x - x_c‖²` once `‖x - x_c‖ ≥ (2 c₄ L / c₃) ‖u - u_eq‖`; then apply Theorem 4.19.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Lemma 4.6.  Differences: the input is measured
from a general `u_eq` (Khalil's is `0`); Khalil asks `f` to be `C¹` and globally Lipschitz in
`(x, u)`; only the regularity of `f(t, x, u_eq)` and the Lipschitz dependence on the input are
used. -/
@[blueprint "lem:continuousSystem-inputToStateStable-of-globallyExponentiallyStable"
  (title := "Exponential stability of the unforced system gives input-to-state stability")
  (latexEnv := "lemma")
  (statement := /-- Let the state space be $\mathbb{R}^n$, $n \ge 1$, let $x_c$ be an equilibrium
    of the system with the input held at $u_{\mathrm{eq}}$, $f(t, x_c, u_{\mathrm{eq}}) = 0$, with
    $f(t, x, u_{\mathrm{eq}})$ continuously differentiable on $\mathbb{R} \times \mathbb{R}^n$
    and globally Lipschitz in $x$, uniformly in $t$, and let
    $\|f(t, x, u) - f(t, x, u_{\mathrm{eq}})\| \le L\|u - u_{\mathrm{eq}}\|$.  If $x_c$ is
    globally exponentially stable for $\dot x = f(t, x, u_{\mathrm{eq}})$
    (\cref{def:continuousSystem-globallyExponentiallyStable},
    \cref{def:continuousSystem-constInput}), the system is input-to-state stable about
    $(x_c, u_{\mathrm{eq}})$ (\cref{def:continuousSystem-inputToStateStable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Lemma 4.6.  Differences: the input is
    measured from a general $u_{\mathrm{eq}}$ rather than $0$; Khalil asks $f$ to be $C^1$ and
    globally Lipschitz in $(x, u)$; only the regularity of $f(t, x, u_{\mathrm{eq}})$ and the
    Lipschitz dependence on the input are used. -/)
  (proof := /-- Let $V$ be the converse Lyapunov function of $\dot x = f(t, x, u_{\mathrm{eq}})$
    (\cref{thm:continuousSystem-exists-quadraticLyapunov-of-globallyExponentiallyStable}):
    $c_1\|x - x_c\|^2 \le V \le c_2\|x - x_c\|^2$, $\dot V \le -c_3\|x - x_c\|^2$ along
    $f(t, x, u_{\mathrm{eq}})$, and $\|\partial V / \partial x\| \le c_4\|x - x_c\|$.  Along
    $f(t, x, u)$,
    \[
      \dot V \le -c_3\|x - x_c\|^2 + c_4\|x - x_c\|\,L\|u - u_{\mathrm{eq}}\|
        \le -\tfrac{c_3}{2}\|x - x_c\|^2
      \quad \text{for } \|x - x_c\| \ge \tfrac{2c_4 L}{c_3}\|u - u_{\mathrm{eq}}\|,
    \]
    so \cref{thm:continuousSystem-inputToStateStable-of-isISSLyapunov} applies with
    $\alpha_i(r) = c_i r^2$ and $\rho(r) = \tfrac{2c_4L}{c_3}r$. -/)]
theorem inputToStateStable_of_globallyExponentiallyStable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [Nontrivial H]
    {s : ContinuousSystem H U' Y'} {x_c : H} {u_eq : U'} (h_eq : ∀ t : ℝ, s.F t x_c u_eq = 0)
    (hf : ContDiff ℝ 1 (fun p : ℝ × H => s.F p.1 p.2 u_eq))
    (h_lip : ∃ L : NNReal, ∀ t : ℝ, LipschitzWith L (fun x => s.F t x u_eq))
    (h_input : ∃ L : ℝ, ∀ (t : ℝ) (x : H) (w : U'),
      ‖s.F t x w - s.F t x u_eq‖ ≤ L * ‖w - u_eq‖)
    (h_ges : (s.constInput u_eq).GloballyExponentiallyStable x_c) :
    s.InputToStateStable x_c u_eq := by
  obtain ⟨Lu, hLu⟩ := h_input
  -- Step 1. The converse Lyapunov function of `ẋ = f(t, x, u_eq)`.
  obtain ⟨V, ⟨-, hV_diff, -, c₁, hc₁, c₂, hc₂, c₃, hc₃, hV_bd⟩, c₄, hc₄, h_grad⟩ :=
    ContinuousSystem.exists_quadraticLyapunov_of_globallyExponentiallyStable
      (s := s.constInput u_eq) h_eq hf h_lip h_ges
  -- Step 2. The ISS-Lyapunov data: `αᵢ(r) = cᵢ r²`, `ρ(r) = k r`, `W₃ = (c₃/2)‖x - x_c‖²`.
  set k := 2 * c₄ * (|Lu| + 1) / c₃
  have hk : 0 < k := by positivity
  set α₁ := (ClassKInfty.power 2 two_pos).smul c₁ hc₁
  set α₂ := (ClassKInfty.power 2 two_pos).smul c₂ hc₂
  set ρ := (ClassKInfty.power 1 one_pos).smul k hk
  set W₃ : H → ℝ := fun x => c₃ / 2 * ‖x - x_c‖ ^ 2
  have hW₃ : IsPositiveDefiniteOn W₃ x_c univ :=
    IsPositiveDefiniteOn.comp (g := fun r => c₃ / 2 * r ^ 2)
      ⟨by fun_prop, by simp, fun r hr hne => by
        have : 0 < r := lt_of_le_of_ne hr (Ne.symm hne)
        positivity⟩
      (isPositiveDefiniteOn_norm_sub x_c univ)
  refine inputToStateStable_of_isISSLyapunov α₁ α₂ ρ (W₃ := W₃)
    (fun t ht y => hV_diff t ht y (mem_univ y))
    (fun t ht y => ⟨(hV_bd t ht y (mem_univ y)).1, (hV_bd t ht y (mem_univ y)).2.1⟩) hW₃
    fun t ht y w hw => ?_
  -- Step 3. Along the forced system, `V̇` is `V̇` of `ẋ = f(t, x, u_eq)` plus `∂V/∂x · e`, with
  -- `e = f(t, y, w) - f(t, y, u_eq)`; the gain `ρ` makes the second term at most half the first.
  obtain ⟨-, -, h_lie⟩ := hV_bd t ht y (mem_univ y)
  rw [Real.rpow_two] at h_lie
  have hw' : k * ‖w - u_eq‖ ≤ ‖y - x_c‖ := by simpa [ρ, ClassKInfty.smul, ClassKInfty.power,
    ClassKInfty.of_strictMono, Real.rpow_one] using hw
  have h_pert := lieDerivative_le_add_norm_fderiv_mul (V := V) (v := fun t y => s.F t y u_eq)
    (w := fun t y => s.F t y w) (hV_diff t ht y (mem_univ y))
  calc _root_.lieDerivative V (fun t y => s.F t y w) t y
      ≤ (s.constInput u_eq).lieDerivative V t y () +
          ‖fderiv ℝ (V t) y‖ * ‖s.F t y w - s.F t y u_eq‖ := h_pert
    _ ≤ -(c₃ * ‖y - x_c‖ ^ 2) + (c₄ * ‖y - x_c‖) * ((|Lu| + 1) * ‖w - u_eq‖) :=
        add_le_add h_lie (mul_le_mul (h_grad t ht y)
          ((hLu t y w).trans (by gcongr; linarith [le_abs_self Lu])) (norm_nonneg _)
          (mul_nonneg hc₄.le (norm_nonneg _)))
    _ = -(c₃ * ‖y - x_c‖ ^ 2) + c₃ / 2 * ‖y - x_c‖ * (k * ‖w - u_eq‖) := by
        simp only [k]; field_simp
    _ ≤ -(c₃ * ‖y - x_c‖ ^ 2) + c₃ / 2 * ‖y - x_c‖ * ‖y - x_c‖ := by gcongr
    _ = -W₃ y := by simp only [W₃]; ring

end ISSLyapunov

end ContinuousSystem
