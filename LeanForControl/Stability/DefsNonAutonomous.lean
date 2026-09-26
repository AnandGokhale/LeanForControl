import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import LeanForControl.Comparison.ClassK
import LeanForControl.Comparison.ClassKInfty
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.MonotoneContinuity
import Architect

variable {n : ℕ}

/-!
# `Stability.DefsNonAutonomous`

Core definitions for the stability theory of non-autonomous ODEs `ẋ = f(t, x)` on `ℝⁿ`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.).

## Notation

`ℝⁿ` denotes `EuclideanSpace ℝ (Fin n)` throughout this file.

## Contents

* **Trajectories and equilibria** (`IsTrajectoryNA`, `IsEquilibriumNA`).
* **Stability predicates** (`StableNA`, `UniformlyStableNA`, `UnstableNA`,
  `AsymptoticStableNA`, `UniformlyAsymptoticStableNA`,
  `GloballyUniformlyAsymptoticStableNA`).
-/

open Set Filter Topology

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## System primitives -/

/-- A global solution `φ : ℝ → ℝⁿ` of the non-autonomous ODE `ẋ = f(t, x)`,
    defined for all `t ∈ ℝ`. -/
@[blueprint "def:isTrajectoryNA"
  (statement := /-- A \emph{trajectory from $t_{0}$} of the non-autonomous ODE
    $\dot{x} = f(t, x)$ is a map $\varphi$ defined and satisfying
    $\dot{\varphi}(t) = f(t,\varphi(t))$ for every $t \ge t_{0}$. This is the object
    Khalil's definitions refer to as ``the solution $x(t)$'': forward-complete from its
    initial time, with existence assumed rather than proved. -/)]
abbrev IsTrajectoryNA (φ : ℝ → ℝⁿ) (f : ℝ → ℝⁿ → ℝⁿ) (t₀ : ℝ) : Prop :=
  IsIntegralCurveOn φ f (Ici t₀)

/-- The point `x_eq` is an equilibrium of `ẋ = f(t, x)` when `f(t, x_eq) = 0` for all `t`. -/
@[blueprint "def:isEquilibriumNA"
  (statement := /-- A point $x_{\mathrm{eq}} \in \mathbb{R}^{n}$ is an
    \emph{equilibrium} of the non-autonomous ODE $\dot{x} = f(t, x)$ when
    $f(t, x_{\mathrm{eq}}) = 0$ for every $t \in \mathbb{R}$. -/)]
def IsEquilibriumNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ t : ℝ, f t x_eq = 0

/-! ## Uniform convergence times

The estimate that the class-`KL` characterization is built from. It is named here rather than
re-typed at each lemma that assumes it. -/

/-- For every tolerance `η` there is a delay `T(η)`, depending on `η` alone — not on the
initial time `t₀`, and not on which solution — after which every trajectory starting within
`c` of `x_eq` is inside the `η`-ball.

*Local*: the radius `c` confines the claim to a neighbourhood of `x_eq`. The global version
quantifies over every `c`.

This is Khalil (4.17), the attractivity half of uniform asymptotic stability. The delay is
what makes it *uniform*: `Tbar_fn` is the least such `T`, and the whole class-`KL`
construction is built by regularizing it. -/
@[blueprint "def:locallyHasUniformConvergenceTime"
  (statement := /-- The trajectories of $\dot{x} = f(t,x)$ starting within $c$ of
    $x_{\mathrm{eq}}$ \emph{have local uniform convergence times} when for every
    $\eta > 0$ there
    is $T(\eta) > 0$, independent of $t_{0}$ and of the solution, with
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| < \eta
      \qquad \forall\, t \ge t_{0} + T(\eta),
    \]
    for every $t_{0} \ge 0$ and every trajectory $\varphi$ on $[t_{0},\infty)$ with
    $\|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c$. -/)]
def LocallyHasUniformConvergenceTime (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (c : ℝ) : Prop :=
  ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η

/-- A uniform convergence time exists from *every* radius, not just from one fixed `c`.

This is Khalil (4.18). Writing it as the local property at every radius, rather than
spelling the quantifiers out again, is what makes it usable: applying it at a radius
*is* the local property there, so the narrowing step that the global proofs need becomes
a function application instead of a hand-built term. -/
@[blueprint "def:globallyHasUniformConvergenceTime"
  (statement := /-- The trajectories of $\dot{x} = f(t,x)$ \emph{have global uniform
    convergence times} when they have local uniform convergence times
    (\cref{def:locallyHasUniformConvergenceTime}) from every radius $c > 0$. The delay may
    depend on the radius as well as the tolerance, $T = T(\eta, c)$. -/)]
def GloballyHasUniformConvergenceTime (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ c > 0, LocallyHasUniformConvergenceTime f x_eq c

/-! ## Comparison-function bounds -/

/-- Every trajectory starting within `a` of `x_eq` is bounded by `α` applied to its own
initial deviation.

*Uniform*: one `α` works for every initial time `t₀` and every trajectory — it is the
trajectories, collectively, that are bounded, not `f`.

The radius `a` is read off `α : ClassK a b` rather than passed separately: a class `K`
function is defined on `[0, a)`, so the locality of the bound is already carried by the
type of the bound.

This is Khalil (4.19), the estimate that characterizes uniform stability. -/
@[blueprint "def:hasUniformClassKBound"
  (statement := /-- The trajectories of $\dot{x} = f(t,x)$ \emph{have the uniform class
    $\mathcal{K}$ bound} $\alpha$ about $x_{\mathrm{eq}}$ when
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le \alpha(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|)
    \]
    for every $t_{0} \ge 0$, every trajectory $\varphi$ on $[t_{0},\infty)$ with
    $\|\varphi(t_{0}) - x_{\mathrm{eq}}\| < a$, and every $t \ge t_{0}$. -/)]
def HasUniformClassKBound (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) {a b : ℝ} (α : ClassK a b) : Prop :=
  ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ →
    ‖φ t₀ - x_eq‖ < a → ∀ t ≥ t₀, ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖

/-- The same estimate with a class `K∞` bound, hence for every initial state: a class `K∞`
function is defined on all of `[0, ∞)`, so no radius restriction survives.

This is Khalil (4.20) in its class `K∞` form, the estimate behind the *global* results. -/
@[blueprint "def:hasUniformClassKInftyBound"
  (statement := /-- The trajectories of $\dot{x} = f(t,x)$ \emph{have the uniform class
    $\mathcal{K}_{\infty}$ bound} $\alpha$ about $x_{\mathrm{eq}}$ when
    $\|\varphi(t) - x_{\mathrm{eq}}\| \le \alpha(\|\varphi(t_{0}) - x_{\mathrm{eq}}\|)$
    for every $t_{0} \ge 0$, every trajectory $\varphi$ on $[t_{0},\infty)$, and every
    $t \ge t_{0}$, with no restriction on the initial state. -/)]
def HasUniformClassKInftyBound (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) (α : ClassKInfty) : Prop :=
  ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ →
    ∀ t ≥ t₀, ‖φ t - x_eq‖ ≤ α.toFun ‖φ t₀ - x_eq‖

/-! ## Stability predicates -/

/-- The equilibrium `x_eq` of `ẋ = f(t, x)` is **stable**: for each `ε > 0` and each
    initial time `t₀ ≥ 0`, there is `δ = δ(ε, t₀) > 0` such that every trajectory from
    `t₀` starting within `δ` of `x_eq` remains within `ε` of `x_eq` for all `t ≥ t₀`.

    This is Khalil (4.16). The hypothesis `IsTrajectoryNA φ f t₀` carries the existence
    assumption that Khalil leaves ambient: the claim constrains those solutions that are
    defined on `[t₀, ∞)`, and says nothing about a system whose solutions escape. Any
    theorem *concluding* this predicate must therefore supply that existence itself —
    see `exists_unique_trajectory`. -/
@[blueprint "def:stableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(t,x)$ is
    \emph{stable} when
    \[
      \forall \varepsilon > 0,\;\forall t_{0} \ge 0,\;
      \exists\,\delta = \delta(\varepsilon,t_{0}) > 0,\;
      \forall \varphi \text{ on } [t_{0},\infty),\;
      \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < \delta
      \;\Rightarrow\; \forall t \ge t_{0},\;
      \|\varphi(t) - x_{\mathrm{eq}}\| < \varepsilon.
    \] -/)]
def StableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∀ t₀ : ℝ, 0 ≤ t₀ →
    ∃ δ > 0, ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < δ →
        ∀ t ≥ t₀, ‖φ t - x_eq‖ < ε

/-- The equilibrium `x_eq` is **uniformly stable**: `δ` can be chosen independently of `t₀`. -/
@[blueprint "def:uniformlyStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{uniformly stable} when
    $\delta$ in \cref{def:stableNA} can be chosen independently of $t_{0}$:
    \[
      \forall \varepsilon > 0,\;\exists\,\delta = \delta(\varepsilon) > 0,\;
      \forall t_{0} \ge 0,\;\forall \varphi \text{ on } [t_{0},\infty),\;
      \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < \delta
      \;\Rightarrow\; \forall t \ge t_{0},\;
      \|\varphi(t) - x_{\mathrm{eq}}\| < \varepsilon.
    \] -/)]
def UniformlyStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < δ →
      ∀ t ≥ t₀, ‖φ t - x_eq‖ < ε

/-- The equilibrium `x_eq` is **globally uniformly stable**: uniformly stable, with the
margin `δ(ε)` growing without bound, so that the basin exhausts `ℝⁿ`.

This is the stability half of Khalil's global uniform asymptotic stability. -/
@[blueprint "def:globallyUniformlyStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{globally uniformly stable}
    when it is uniformly stable (\cref{def:uniformlyStableNA}) with a margin
    $\delta(\varepsilon)$ that can be chosen to satisfy
    $\lim_{\varepsilon \to \infty} \delta(\varepsilon) = \infty$. -/)]
def GloballyUniformlyStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ δ : ℝ → ℝ,
    (∀ ε > 0, 0 < δ ε) ∧
    Filter.Tendsto δ Filter.atTop Filter.atTop ∧
    ∀ ε > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < δ ε → ∀ t ≥ t₀, ‖φ t - x_eq‖ < ε

/-- Global uniform stability is stability. -/
lemma GloballyUniformlyStableNA.stableNA {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : GloballyUniformlyStableNA f x_eq) : StableNA f x_eq :=
  fun ε hε t₀ ht₀ =>
    let ⟨δ, hδ_pos, _, hstab⟩ := h; ⟨δ ε, hδ_pos ε hε, hstab ε hε t₀ ht₀⟩

/-- The equilibrium `x_eq` is **unstable** if it is not stable. -/
@[blueprint "def:unstableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{unstable} when it is not
    stable (\cref{def:stableNA}). -/)]
def UnstableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop := ¬ StableNA f x_eq

/-- Uniform stability is stability: the uniform `δ` already works at every initial time. -/
lemma UniformlyStableNA.stableNA {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ}
    (h : UniformlyStableNA f x_eq) : StableNA f x_eq :=
  fun ε hε t₀ ht₀ => let ⟨δ, hδ, hstab⟩ := h ε hε; ⟨δ, hδ, hstab t₀ ht₀⟩

/-- A trajectory sitting *at* a stable equilibrium cannot leave it.

Note the hypothesis is stability, not `IsEquilibriumNA`. "An equilibrium stays put" does
**not** follow from `f t x_eq = 0` alone — it also needs uniqueness of solutions. Without
uniqueness a solution can leave an equilibrium: `ẋ = x^{2/3}` has `f 0 = 0`, yet both
`x ≡ 0` and `x = (t/3)³` solve it from `x 0 = 0`.

Stability supplies the conclusion directly and at weaker hypotheses: the trajectory is
within `ε` of `x_eq` for *every* `ε > 0`, hence at distance zero. -/
lemma IsTrajectoryNA.eq_of_stableNA {f : ℝ → ℝⁿ → ℝⁿ} {x_eq : ℝⁿ} {φ : ℝ → ℝⁿ} {t₀ : ℝ}
    (hS : StableNA f x_eq) (hφ : IsTrajectoryNA φ f t₀) (ht₀ : 0 ≤ t₀)
    (h0 : φ t₀ = x_eq) {t : ℝ} (ht : t₀ ≤ t) :
    φ t = x_eq := by
  have hlt : ∀ ε > 0, ‖φ t - x_eq‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hstab⟩ := hS ε hε t₀ ht₀
    exact hstab φ hφ (by simpa [h0] using hδ) t ht
  have : ‖φ t - x_eq‖ ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by simpa using (hlt ε hε).le
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

/-- The equilibrium `x_eq` is **asymptotically stable**: stable, and for each `t₀ ≥ 0`
    there is `c = c(t₀) > 0` such that every trajectory starting within `c` of `x_eq`
    at `t₀` converges to `x_eq` as `t → ∞`. -/
@[blueprint "def:asymptoticStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{asymptotically stable}
    when it is stable (\cref{def:stableNA}) and for each $t_{0} \ge 0$ there exists
    $c = c(t_{0}) > 0$ such that every solution defined for all forward time with
    $\|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c$ satisfies
    $\varphi(t) \to x_{\mathrm{eq}}$ as $t \to \infty$.

    Attractivity quantifies over forward-complete solutions, as convergence must; the
    completeness restriction is harmless because the stability conjunct guards it. -/)]
def AsymptoticStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  StableNA f x_eq ∧
  ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ c > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < c →
      Filter.Tendsto φ Filter.atTop (nhds x_eq)

/-- The equilibrium `x_eq` is **uniformly asymptotically stable**: uniformly stable, and
    there is `c > 0`, independent of `t₀`, such that for each `η > 0` there is
    `T = T(η) > 0` with `‖φ(t) - x_eq‖ < η` for all `t ≥ t₀ + T(η)`, uniformly over
    trajectories starting within `c` and all `t₀ ≥ 0`. -/
@[blueprint "def:uniformlyAsymptoticStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{uniformly asymptotically
    stable} when it is uniformly stable (\cref{def:uniformlyStableNA}) and there exists
    $c > 0$ (independent of $t_{0}$) such that for each $\eta > 0$ there is
    $T = T(\eta) > 0$ with
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| < \eta \quad
      \forall\, t \ge t_{0}+T(\eta),\;
      \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c,\;
      \forall\, t_{0} \ge 0.
    \] -/)]
def UniformlyAsymptoticStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  UniformlyStableNA f x_eq ∧ ∃ c > 0, LocallyHasUniformConvergenceTime f x_eq c

/-- The equilibrium `x_eq` is **globally uniformly asymptotically stable**: uniformly stable
    with `δ(ε) → ∞` as `ε → ∞` (so the attraction basin is all of `ℝⁿ`), and for each
    pair `η, c > 0` there is `T = T(η, c) > 0` such that `‖φ(t) - x_eq‖ < η` for all
    `t ≥ t₀ + T(η, c)` and all trajectories starting within `c` of `x_eq`. -/
@[blueprint "def:globallyUniformlyAsymptoticStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{globally uniformly
    asymptotically stable} when it is uniformly stable with $\delta(\varepsilon) \to \infty$
    as $\varepsilon \to \infty$, and for each pair of positive numbers $\eta$ and $c$
    there is $T = T(\eta,c) > 0$ such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| < \eta \quad
      \forall\, t \ge t_{0}+T(\eta,c),\;
      \forall\, \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c,\;
      \forall\, t_{0} \ge 0.
    \] -/)]
def GloballyUniformlyAsymptoticStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  GloballyUniformlyStableNA f x_eq ∧ GloballyHasUniformConvergenceTime f x_eq

/-- The equilibrium `x_eq` is **exponentially stable**: there exist positive constants
    `c`, `k`, and `λ` such that every trajectory starting within `c` of `x_eq` satisfies
    the exponential bound `‖φ(t) - x_eq‖ ≤ k ‖φ(t₀) - x_eq‖ · exp(-λ(t - t₀))`
    for all `t ≥ t₀`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.). -/
@[blueprint "def:exponentiallyStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{exponentially stable}
    when there exist positive constants $c$, $k$, and $\lambda$ such that
    \[
      \|\varphi(t) - x_{\mathrm{eq}}\| \le k\,\|\varphi(t_{0}) - x_{\mathrm{eq}}\|\,
      e^{-\lambda(t - t_{0})}
    \]
    for all $t \ge t_{0} \ge 0$ and all trajectories $\varphi$ on $[t_{0},\infty)$
    with $\|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c$. -/)]
def ExponentiallyStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ c > 0, ∃ k > 0, ∃ γ > 0,
    ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f t₀ → ‖φ t₀ - x_eq‖ < c →
        ∀ t ≥ t₀, ‖φ t - x_eq‖ ≤ k * ‖φ t₀ - x_eq‖ * Real.exp (-γ * (t - t₀))

/-- The equilibrium `x_eq` is **globally exponentially stable**: the exponential bound
    holds for any initial state, with no restriction on `‖φ(t₀) - x_eq‖`. -/
@[blueprint "def:globallyExponentiallyStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{globally exponentially
    stable} when the bound in \cref{def:exponentiallyStableNA} holds for every initial
    state $\varphi(t_{0}) \in \mathbb{R}^{n}$, i.e., $c = \infty$. -/)]
def GloballyExponentiallyStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ k > 0, ∃ γ > 0,
    ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f t₀ →
        ∀ t ≥ t₀, ‖φ t - x_eq‖ ≤ k * ‖φ t₀ - x_eq‖ * Real.exp (-γ * (t - t₀))

/-! ## Existence of trajectories (Picard-Lindelöf) -/

/-- **Picard-Lindelöf / Lindelöf-Picard (global existence and uniqueness)**.

    For a jointly continuous vector field `f : ℝ → ℝⁿ → ℝⁿ` that is locally
    Lipschitz in the state variable, uniformly on compact time sets, through every
    initial condition `(t₀, x₀)` there passes a **unique** global trajectory
    satisfying `ẋ = f(t, x)`.

    **Remark on global existence**: local Lipschitz continuity yields existence on a
    maximal interval `[t₀, t_max)`.  To guarantee `t_max = +∞` (no finite-time blowup)
    one needs an additional condition such as:
    - linear growth `‖f(t, x)‖ ≤ C · (1 + ‖x‖)`, or
    - a forward-invariant compact set containing the trajectory.

    This axiom packages both conditions under the assumption that solutions are
    complete; the user must verify that for any concrete `f`, e.g., by exhibiting a
    Lyapunov bound that prevents blowup. -/
axiom exists_unique_trajectory
    (f : ℝ → ℝⁿ → ℝⁿ)
    (hf_cont : Continuous (Function.uncurry f))
    (hf_lip : ∀ K : Set ℝ, IsCompact K → ∃ L : NNReal, ∀ t ∈ K, LipschitzWith L (f t))
    (t₀ : ℝ) (x₀ : ℝⁿ) :
    ∃! φ : ℝ → ℝⁿ, IsTrajectoryNA φ f t₀ ∧ φ t₀ = x₀
