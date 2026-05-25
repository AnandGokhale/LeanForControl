import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.MonotoneContinuity
import Architect

variable {n : ℕ}

/-!
# `Stability.DefsNonAutonomous`

Core definitions for the stability theory of non-autonomous ODEs `ẋ = f(t, x)` on `ℝⁿ`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4.

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
  (statement := /-- A \emph{trajectory} of the non-autonomous ODE $\dot{x} = f(t, x)$
    is a globally defined map $\varphi : \mathbb{R} \to \mathbb{R}^{n}$ satisfying
    \[
      \dot{\varphi}(t) = f(t,\varphi(t)) \qquad \text{for every } t \in \mathbb{R}.
    \] -/)]
def IsTrajectoryNA (φ : ℝ → ℝⁿ) (f : ℝ → ℝⁿ → ℝⁿ) : Prop :=
  ∀ t : ℝ, HasDerivAt φ (f t (φ t)) t

/-- The point `x_eq` is an equilibrium of `ẋ = f(t, x)` when `f(t, x_eq) = 0` for all `t`. -/
@[blueprint "def:isEquilibriumNA"
  (statement := /-- A point $x_{\mathrm{eq}} \in \mathbb{R}^{n}$ is an
    \emph{equilibrium} of the non-autonomous ODE $\dot{x} = f(t, x)$ when
    $f(t, x_{\mathrm{eq}}) = 0$ for every $t \in \mathbb{R}$. -/)]
def IsEquilibriumNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ t : ℝ, f t x_eq = 0

/-! ## Stability predicates -/

/-- The equilibrium `x_eq` of `ẋ = f(t, x)` is **stable**: for each `ε > 0` and each
    initial time `t₀ ≥ 0`, there is `δ = δ(ε, t₀) > 0` such that every trajectory
    starting within `δ` of `x_eq` at time `t₀` remains within `ε` of `x_eq` for all
    `t ≥ t₀`. -/
@[blueprint "def:stableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of $\dot{x} = f(t,x)$ is
    \emph{stable} when
    \[
      \forall \varepsilon > 0,\;\forall t_{0} \ge 0,\;
      \exists\,\delta = \delta(\varepsilon,t_{0}) > 0,\;
      \forall \varphi,\;\mathrm{IsTrajectoryNA}(\varphi,f)
      \;\Rightarrow\; \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < \delta
      \;\Rightarrow\; \forall t \ge t_{0},\;\|\varphi(t) - x_{\mathrm{eq}}\| < \varepsilon.
    \] -/)]
def StableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∀ t₀ : ℝ, 0 ≤ t₀ →
    ∃ δ > 0, ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < δ → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ < ε

/-- The equilibrium `x_eq` is **uniformly stable**: `δ` can be chosen independently of `t₀`. -/
@[blueprint "def:uniformlyStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{uniformly stable} when
    $\delta$ in \cref{def:stableNA} can be chosen independently of $t_{0}$:
    \[
      \forall \varepsilon > 0,\;\exists\,\delta = \delta(\varepsilon) > 0,\;
      \forall t_{0} \ge 0,\;\forall \varphi,\;\mathrm{IsTrajectoryNA}(\varphi,f)
      \;\Rightarrow\; \|\varphi(t_{0}) - x_{\mathrm{eq}}\| < \delta
      \;\Rightarrow\; \forall t \ge t_{0},\;\|\varphi(t) - x_{\mathrm{eq}}\| < \varepsilon.
    \] -/)]
def UniformlyStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < δ → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ < ε

/-- The equilibrium `x_eq` is **unstable** if it is not stable. -/
@[blueprint "def:unstableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{unstable} when it is not
    stable (\cref{def:stableNA}). -/)]
def UnstableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop := ¬ StableNA f x_eq

/-- The equilibrium `x_eq` is **asymptotically stable**: stable, and for each `t₀ ≥ 0`
    there is `c = c(t₀) > 0` such that every trajectory starting within `c` of `x_eq`
    at `t₀` converges to `x_eq` as `t → ∞`. -/
@[blueprint "def:asymptoticStableNA"
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ is \emph{asymptotically stable}
    when it is stable (\cref{def:stableNA}) and for each $t_{0} \ge 0$ there exists
    $c = c(t_{0}) > 0$ such that every trajectory $\varphi$ with
    $\|\varphi(t_{0}) - x_{\mathrm{eq}}\| < c$ satisfies
    $\varphi(t) \to x_{\mathrm{eq}}$ as $t \to \infty$. -/)]
def AsymptoticStableNA (f : ℝ → ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  StableNA f x_eq ∧
  ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ c > 0, ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → Filter.Tendsto φ Filter.atTop (nhds x_eq)

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
  UniformlyStableNA f x_eq ∧
  ∃ c > 0, ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η

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
  (∃ δ : ℝ → ℝ,
    (∀ ε > 0, 0 < δ ε) ∧
    Filter.Tendsto δ Filter.atTop Filter.atTop ∧
    ∀ ε > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
      IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < δ ε → ∀ t : ℝ, t₀ ≤ t → ‖φ t - x_eq‖ < ε) ∧
  ∀ η > 0, ∀ c > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ φ : ℝ → ℝⁿ,
    IsTrajectoryNA φ f → ‖φ t₀ - x_eq‖ < c → ∀ t : ℝ, t₀ + T ≤ t → ‖φ t - x_eq‖ < η
