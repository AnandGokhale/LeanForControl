import LeanForControl.Systems.Continuous
import Mathlib.Analysis.SpecialFunctions.Exp
import Architect

/-!
# `Stability.Continuous.Defs` — stability of continuous-time systems

Stability notions for an equilibrium `x_eq` of an autonomous (input-free) continuous-time system
`ẋ = f(t, x)`, as a `ContinuousSystem E Unit Y`.  A system with input is unforced first, by
`ContinuousSystem.zeroInput`; input–output notions such as input-to-state stability are separate
and not defined here.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definitions 4.4–4.6.

## One definition per notion

Each notion is defined once, for time-varying systems, with the initial time `t₀ ≥ 0` explicit.
A time-invariant system is a special case, not a separate definition; that its notions may be
read with `t₀ = 0` is a theorem about time-invariant systems.

* **Non-uniform** (constants may depend on `t₀`): `Stable`, `LocallyAsymptoticallyStable`,
  `GloballyAsymptoticallyStable`, and `Unstable`.
* **Uniform** (constants independent of `t₀`): `UniformlyStable`,
  `UniformlyAsymptoticallyStable`, `GloballyUniformlyStable`,
  `GloballyUniformlyAsymptoticallyStable`.
* **Exponential**, uniform as in Khalil's Definition 4.5: `LocallyExponentiallyStable`,
  `GloballyExponentiallyStable`.

For time-invariant systems uniform and non-uniform notions coincide; for time-varying ones they
differ (`ẋ = -x / (1 + t)` is globally asymptotically but not uniformly asymptotically stable).

## Which trajectories are quantified over

* **Bounds** — stability, uniform convergence times, exponential estimates — quantify over
  trajectories on *segments* `[t₀, t₁]`.  A solution that escapes in finite time is then not
  silently excluded: its segments still have to satisfy the bound, so finite escape near the
  equilibrium counts against stability.
* **Limits** — the attractivity part of `LocallyAsymptoticallyStable` and
  `GloballyAsymptoticallyStable` — quantify over trajectories on *rays* `[t₀, ∞)`, since a limit
  needs the whole forward time axis.  Those notions also require forward completeness
  (`ContinuousSystem.IsForwardCompleteOn`) from the same initial states: otherwise a solution
  that escapes in finite time has no ray to converge on and would be silently left out.
* **Ultimate bounds** — `UniformlyUltimatelyBounded` and `GloballyUniformlyUltimatelyBounded` —
  quantify over rays and require forward completeness too.  They constrain only times after
  `t₀ + T`, so on segments a solution escaping before then would pass untested.  Khalil leaves
  this completeness implicit.

Uniqueness of solutions is never required: every notion quantifies over *every* solution, which
is the stronger reading when solutions are not unique.  Theorems that need uniqueness assume
`ContinuousSystem.HasUniqueSolutions`.

## Conventions

* Inequalities are strict, as in Khalil, except in the boundedness notions, which follow
  Khalil's non-strict Definition 4.6.
* The equilibrium is a general `x_eq`; Khalil places it at the origin.  The boundedness notions
  are about a general point `x_c`, which need not be an equilibrium.
* The output space `Y` plays no role.
-/

open Set Filter Topology

namespace ContinuousSystem

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Stability and instability -/

/-- The equilibrium `x_eq` is **stable**: for every `ε > 0` and initial time `t₀ ≥ 0` there is
`δ > 0` such that every trajectory starting within `δ` of `x_eq` at `t₀` stays within `ε` of it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4 (*stable*). -/
@[blueprint "def:continuousSystem-stable"
  (title := "Stability")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of an autonomous continuous-time system
    $\dot x = f(t, x)$ is \emph{stable} when for every $\varepsilon > 0$ and $t_0 \ge 0$ there is
    $\delta = \delta(\varepsilon, t_0) > 0$ such that every trajectory on a segment $[t_0, t_1]$
    with $\|x(t_0) - x_{\mathrm{eq}}\| < \delta$ satisfies
    $\|x(t) - x_{\mathrm{eq}}\| < \varepsilon$ for all $t \in [t_0, t_1]$.

    Quantifying over segments rather than over solutions on $[t_0, \infty)$ means a solution that
    escapes in finite time counts against stability instead of being silently excluded.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4 (\emph{stable}). -/)]
def Stable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  ∀ ε > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ δ > 0, ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < δ →
      ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < ε

/-- The equilibrium `x_eq` is **unstable** when it is not stable.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4 (*unstable*). -/
@[blueprint "def:continuousSystem-unstable"
  (title := "Instability")
  (statement := /-- The equilibrium is \emph{unstable} when it is not stable
    (\cref{def:continuousSystem-stable}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4. -/)]
def Unstable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  ¬ s.Stable x_eq

/-- The equilibrium `x_eq` is **uniformly stable**: `δ` in `Stable` can be chosen independently
of the initial time.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4 (*uniformly stable*). -/
@[blueprint "def:continuousSystem-uniformlyStable"
  (title := "Uniform stability")
  (statement := /-- The equilibrium is \emph{uniformly stable} when $\delta$ in
    \cref{def:continuousSystem-stable} can be chosen independently of $t_0$:
    $\delta = \delta(\varepsilon)$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4
    (\emph{uniformly stable}). -/)]
def UniformlyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < δ →
      ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < ε

/-- The equilibrium `x_eq` is **globally uniformly stable**: uniformly stable, with a choice of
`δ(ε)` that grows without bound.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4 (*globally uniformly
asymptotically stable*, its stability half). -/
@[blueprint "def:continuousSystem-globallyUniformlyStable"
  (title := "Global uniform stability")
  (statement := /-- The equilibrium is \emph{globally uniformly stable} when it is uniformly
    stable (\cref{def:continuousSystem-uniformlyStable}) with a choice of $\delta(\varepsilon)$
    satisfying $\delta(\varepsilon) \to \infty$ as $\varepsilon \to \infty$.  In particular every
    trajectory is bounded, so none escapes in finite time.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4. -/)]
def GloballyUniformlyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  ∃ δ : ℝ → ℝ, (∀ ε > 0, 0 < δ ε) ∧ Tendsto δ atTop atTop ∧
    ∀ ε > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < δ ε →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ < ε

/-! ## Asymptotic stability -/

/-- The equilibrium `x_eq` is **locally asymptotically stable**: stable, and for every initial
time `t₀ ≥ 0` there is `c > 0` such that solutions starting within `c` of `x_eq` exist for all
forward time and converge to it.  This is Khalil's *asymptotically stable*.

Forward completeness is part of the definition: without it, a solution that escapes in finite
time has no ray to converge on and would not be tested.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4 (*asymptotically stable*). -/
@[blueprint "def:continuousSystem-locallyAsymptoticallyStable"
  (title := "Local asymptotic stability")
  (statement := /-- The equilibrium is \emph{locally asymptotically stable} when it is stable
    (\cref{def:continuousSystem-stable}) and for every $t_0 \ge 0$ there is $c = c(t_0) > 0$ such
    that the system is forward complete from the ball of radius $c$ about $x_{\mathrm{eq}}$ at
    $t_0$ (\cref{def:continuousSystem-isForwardCompleteOn}) and every trajectory on
    $[t_0, \infty)$ starting in that ball satisfies $x(t) \to x_{\mathrm{eq}}$.  Forward
    completeness keeps solutions that escape in finite time from being silently excluded.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4
    (\emph{asymptotically stable}). -/)]
def LocallyAsymptoticallyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  s.Stable x_eq ∧ ∀ t₀ : ℝ, 0 ≤ t₀ → ∃ c > 0,
    s.IsForwardCompleteOn (fun _ => ()) t₀ (Metric.ball x_eq c) ∧
    ∀ x : ℝ → E, s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → ‖x t₀ - x_eq‖ < c →
      Tendsto x atTop (𝓝 x_eq)

/-- The equilibrium `x_eq` is **globally asymptotically stable**: stable, and every solution
exists for all forward time and converges to it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Section 4.1 (*globally asymptotically
stable*), in the time-varying setting of Definition 4.4. -/
@[blueprint "def:continuousSystem-globallyAsymptoticallyStable"
  (title := "Global asymptotic stability")
  (statement := /-- The equilibrium is \emph{globally asymptotically stable} when it is stable
    (\cref{def:continuousSystem-stable}), the system is forward complete from every state at
    every $t_0 \ge 0$ (\cref{def:continuousSystem-isForwardCompleteOn}), and every trajectory on
    $[t_0, \infty)$ satisfies $x(t) \to x_{\mathrm{eq}}$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Section 4.1. -/)]
def GloballyAsymptoticallyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  s.Stable x_eq ∧ ∀ t₀ : ℝ, 0 ≤ t₀ → s.IsForwardCompleteOn (fun _ => ()) t₀ univ ∧
    ∀ x : ℝ → E, s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → Tendsto x atTop (𝓝 x_eq)

/-- Trajectories starting within `c` of `x_eq` are within any `η > 0` of it after a time `T(η)`
that depends neither on the initial time nor on the trajectory.  The convergence half of the
uniform asymptotic notions. -/
@[blueprint "def:continuousSystem-hasUniformConvergenceTime"
  (title := "Uniform convergence time")
  (statement := /-- Trajectories starting within $c$ of $x_{\mathrm{eq}}$ have a \emph{uniform
    convergence time}: for every $\eta > 0$ there is $T = T(\eta) > 0$ such that every
    trajectory on a segment $[t_0, t_1]$, $t_0 \ge 0$, with $\|x(t_0) - x_{\mathrm{eq}}\| < c$
    satisfies $\|x(t) - x_{\mathrm{eq}}\| < \eta$ for $t \in [t_0 + T, t_1]$. -/)]
def HasUniformConvergenceTime (s : ContinuousSystem E Unit Y) (x_eq : E) (c : ℝ) : Prop :=
  ∀ η > 0, ∃ T > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
      ∀ t ∈ Icc (t₀ + T) t₁, ‖x t - x_eq‖ < η

/-- The equilibrium `x_eq` is **uniformly asymptotically stable**: uniformly stable, with a
uniform convergence time from some ball around it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4 (*uniformly asymptotically
stable*). -/
@[blueprint "def:continuousSystem-uniformlyAsymptoticallyStable"
  (title := "Uniform asymptotic stability")
  (statement := /-- The equilibrium is \emph{uniformly asymptotically stable} when it is
    uniformly stable (\cref{def:continuousSystem-uniformlyStable}) and there is $c > 0$ from
    which convergence has a uniform convergence time
    (\cref{def:continuousSystem-hasUniformConvergenceTime}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4
    (\emph{uniformly asymptotically stable}). -/)]
def UniformlyAsymptoticallyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  s.UniformlyStable x_eq ∧ ∃ c > 0, s.HasUniformConvergenceTime x_eq c

/-- The equilibrium `x_eq` is **globally uniformly asymptotically stable**: globally uniformly
stable, with a uniform convergence time from every ball around it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4 (*globally uniformly
asymptotically stable*). -/
@[blueprint "def:continuousSystem-globallyUniformlyAsymptoticallyStable"
  (title := "Global uniform asymptotic stability")
  (statement := /-- The equilibrium is \emph{globally uniformly asymptotically stable} when it is
    globally uniformly stable (\cref{def:continuousSystem-globallyUniformlyStable}) and every
    $c > 0$ admits a uniform convergence time
    (\cref{def:continuousSystem-hasUniformConvergenceTime}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4. -/)]
def GloballyUniformlyAsymptoticallyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  s.GloballyUniformlyStable x_eq ∧ ∀ c > 0, s.HasUniformConvergenceTime x_eq c

/-! ## Exponential stability -/

/-- The equilibrium `x_eq` is **locally exponentially stable**: there are `c, k, γ > 0` such that
every trajectory starting within `c` of `x_eq` satisfies
`‖x(t) - x_eq‖ ≤ k ‖x(t₀) - x_eq‖ e^{-γ (t - t₀)}`.  The constants do not depend on `t₀`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.5. -/
@[blueprint "def:continuousSystem-locallyExponentiallyStable"
  (title := "Local exponential stability")
  (statement := /-- The equilibrium is \emph{locally exponentially stable} when there are
    $c, k, \gamma > 0$ such that every trajectory on a segment $[t_0, t_1]$, $t_0 \ge 0$, with
    $\|x(t_0) - x_{\mathrm{eq}}\| < c$ satisfies
    \[
      \|x(t) - x_{\mathrm{eq}}\| \le k\,\|x(t_0) - x_{\mathrm{eq}}\|\,e^{-\gamma (t - t_0)}
      \qquad \forall\, t \in [t_0, t_1].
    \]
    The constants do not depend on $t_0$: exponential stability is uniform, as in the
    reference.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.5. -/)]
def LocallyExponentiallyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  ∃ c > 0, ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
      ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀))

/-- The equilibrium `x_eq` is **globally exponentially stable**: the exponential estimate holds
for every initial state.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.5. -/
@[blueprint "def:continuousSystem-globallyExponentiallyStable"
  (title := "Global exponential stability")
  (statement := /-- The equilibrium is \emph{globally exponentially stable} when the estimate of
    \cref{def:continuousSystem-locallyExponentiallyStable} holds for every initial state, with no
    radius $c$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.5. -/)]
def GloballyExponentiallyStable (s : ContinuousSystem E Unit Y) (x_eq : E) : Prop :=
  ∃ k > 0, ∃ γ > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) →
      ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀))

/-! ## Boundedness -/

/-- Trajectories are **uniformly bounded** around `x_c`: there is `c > 0` such that for every
`a < c` a bound `β(a)` holds for all trajectories starting within `a` of `x_c`.  A property of the
system rather than of an equilibrium: `x_c` need not be one.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.6 (*uniformly bounded*). -/
@[blueprint "def:continuousSystem-uniformlyBounded"
  (title := "Uniform boundedness")
  (statement := /-- Trajectories are \emph{uniformly bounded} around $x_c$ when there is $c > 0$
    such that for every $0 < a < c$ there is $\beta = \beta(a) > 0$ with
    \[
      \|x(t_0) - x_c\| \le a \;\Rightarrow\;
      \|x(t) - x_c\| \le \beta \qquad \forall\, t \in [t_0, t_1]
    \]
    for every trajectory on a segment $[t_0, t_1]$, $t_0 \ge 0$.  The point $x_c$ need not be an
    equilibrium.  The bound applies to every segment a solution exists on, so finite escape
    violates it.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.6. -/)]
def UniformlyBounded (s : ContinuousSystem E Unit Y) (x_c : E) : Prop :=
  ∃ c > 0, ∀ a, 0 < a → a < c → ∃ β > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_c‖ ≤ a →
      ∀ t ∈ Icc t₀ t₁, ‖x t - x_c‖ ≤ β

/-- Trajectories are **globally uniformly bounded** around `x_c`: `UniformlyBounded` for every
initial radius `a`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.6 (*globally uniformly
bounded*). -/
@[blueprint "def:continuousSystem-globallyUniformlyBounded"
  (title := "Global uniform boundedness")
  (statement := /-- Trajectories are \emph{globally uniformly bounded} around $x_c$ when the bound
    of \cref{def:continuousSystem-uniformlyBounded} holds for every $a > 0$, with no radius $c$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.6. -/)]
def GloballyUniformlyBounded (s : ContinuousSystem E Unit Y) (x_c : E) : Prop :=
  ∀ a > 0, ∃ β > 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
    s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_c‖ ≤ a →
      ∀ t ∈ Icc t₀ t₁, ‖x t - x_c‖ ≤ β

/-- Trajectories are **uniformly ultimately bounded** with ultimate bound `b` around `x_c`: there
is `c > 0` such that the system is forward complete from the ball of radius `c` about `x_c`, and
for every `a < c` a time `T(a, b)` brings every trajectory starting within `a` of `x_c` to within
`b` of it.

Forward completeness is part of the definition: the bound only constrains times after `t₀ + T`,
so a solution escaping before then would otherwise pass untested.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.6 (*uniformly ultimately
bounded*). -/
@[blueprint "def:continuousSystem-uniformlyUltimatelyBounded"
  (title := "Uniform ultimate boundedness")
  (statement := /-- Trajectories are \emph{uniformly ultimately bounded} with ultimate bound $b$
    around $x_c$ when there is $c > 0$ such that for every $t_0 \ge 0$ the system is forward
    complete from the ball of radius $c$ about $x_c$
    (\cref{def:continuousSystem-isForwardCompleteOn}), and for every $0 < a < c$ there is
    $T = T(a, b) \ge 0$ with
    \[
      \|x(t_0) - x_c\| \le a \;\Rightarrow\; \|x(t) - x_c\| \le b \qquad \forall\, t \ge t_0 + T
    \]
    for every trajectory on $[t_0, \infty)$.  The point $x_c$ need not be an equilibrium.
    Khalil leaves forward completeness implicit; without it, a solution escaping before
    $t_0 + T$ would never be tested.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.6. -/)]
def UniformlyUltimatelyBounded (s : ContinuousSystem E Unit Y) (x_c : E) (b : ℝ) : Prop :=
  ∃ c > 0, (∀ t₀ : ℝ, 0 ≤ t₀ → s.IsForwardCompleteOn (fun _ => ()) t₀ (Metric.ball x_c c)) ∧
    ∀ a, 0 < a → a < c → ∃ T ≥ 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E,
      s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → ‖x t₀ - x_c‖ ≤ a →
        ∀ t ≥ t₀ + T, ‖x t - x_c‖ ≤ b

/-- Trajectories are **globally uniformly ultimately bounded** with ultimate bound `b` around
`x_c`: the system is forward complete, and `UniformlyUltimatelyBounded` holds for every initial
radius `a`.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.6 (*globally uniformly ultimately
bounded*). -/
@[blueprint "def:continuousSystem-globallyUniformlyUltimatelyBounded"
  (title := "Global uniform ultimate boundedness")
  (statement := /-- Trajectories are \emph{globally uniformly ultimately bounded} with ultimate
    bound $b$ around $x_c$ when the system is forward complete from every state at every
    $t_0 \ge 0$ (\cref{def:continuousSystem-isForwardCompleteOn}) and the ultimate bound of
    \cref{def:continuousSystem-uniformlyUltimatelyBounded} holds for every $a > 0$, with no
    radius $c$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.6. -/)]
def GloballyUniformlyUltimatelyBounded (s : ContinuousSystem E Unit Y) (x_c : E) (b : ℝ) :
    Prop :=
  (∀ t₀ : ℝ, 0 ≤ t₀ → s.IsForwardCompleteOn (fun _ => ()) t₀ univ) ∧
    ∀ a > 0, ∃ T ≥ 0, ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ x : ℝ → E,
      s.IsTrajectoryOn (fun _ => ()) x (Ici t₀) → ‖x t₀ - x_c‖ ≤ a →
        ∀ t ≥ t₀ + T, ‖x t - x_c‖ ≤ b

/-! ## Implications between the notions -/

variable {s : ContinuousSystem E Unit Y} {x_eq : E}

/-- **Instability from a fixed escape radius.**  If for every `δ > 0` some trajectory on a segment
`[0, T]` starts within `δ` of `x_eq` and reaches distance `ε`, then `x_eq` is unstable: stability
at `t₀ = 0` with tolerance `ε` is violated.  This is the form in which instability theorems
produce their witnesses. -/
@[blueprint "lem:continuousSystem-unstable-of-escape"
  (title := "Instability from a fixed escape radius")
  (latexEnv := "lemma")
  (statement := /-- Fix $\varepsilon > 0$.  If for every $\delta > 0$ some trajectory on a segment
    $[0, T]$ starts within $\delta$ of $x_{\mathrm{eq}}$ and reaches distance at least
    $\varepsilon$ from it, then $x_{\mathrm{eq}}$ is unstable
    (\cref{def:continuousSystem-unstable}). -/)
  (proof := /-- Stability at $t_0 = 0$ with tolerance $\varepsilon$ gives a $\delta$; the
    trajectory for that $\delta$ contradicts it. -/)]
lemma unstable_of_escape {ε : ℝ} (hε : 0 < ε)
    (hescape : ∀ δ > 0, ∃ (T : ℝ) (x : ℝ → E) (t : ℝ),
      s.IsTrajectoryOn (fun _ => ()) x (Icc 0 T) ∧ ‖x 0 - x_eq‖ < δ ∧
        t ∈ Icc 0 T ∧ ε ≤ ‖x t - x_eq‖) :
    s.Unstable x_eq := by
  intro h
  obtain ⟨δ, hδ, h_bound⟩ := h ε hε 0 le_rfl
  obtain ⟨T, x, t, hx, hx₀, ht, h_far⟩ := hescape δ hδ
  exact h_far.not_gt (h_bound T x hx hx₀ t ht)

/-- Uniform stability implies stability. -/
@[blueprint "lem:continuousSystem-uniformlyStable-stable"
  (title := "Uniform stability implies stability")
  (latexEnv := "lemma")
  (statement := /-- A uniformly stable equilibrium (\cref{def:continuousSystem-uniformlyStable})
    is stable (\cref{def:continuousSystem-stable}). -/)]
lemma UniformlyStable.stable (h : s.UniformlyStable x_eq) : s.Stable x_eq := fun ε hε t₀ ht₀ => by
  obtain ⟨δ, hδ, h_bound⟩ := h ε hε
  exact ⟨δ, hδ, h_bound t₀ ht₀⟩

/-- Global uniform stability implies uniform stability. -/
lemma GloballyUniformlyStable.uniformlyStable (h : s.GloballyUniformlyStable x_eq) :
    s.UniformlyStable x_eq := fun ε hε => by
  obtain ⟨δ, hδ_pos, -, h_bound⟩ := h
  exact ⟨δ ε, hδ_pos ε hε, h_bound ε hε⟩

/-- Local asymptotic stability implies stability. -/
lemma LocallyAsymptoticallyStable.stable (h : s.LocallyAsymptoticallyStable x_eq) :
    s.Stable x_eq :=
  h.1

/-- Global asymptotic stability implies local asymptotic stability. -/
@[blueprint "lem:continuousSystem-globallyAsymptoticallyStable-local"
  (title := "Global asymptotic stability implies local asymptotic stability")
  (latexEnv := "lemma")
  (statement := /-- A globally asymptotically stable equilibrium
    (\cref{def:continuousSystem-globallyAsymptoticallyStable}) is locally asymptotically stable
    (\cref{def:continuousSystem-locallyAsymptoticallyStable}). -/)]
lemma GloballyAsymptoticallyStable.locallyAsymptoticallyStable
    (h : s.GloballyAsymptoticallyStable x_eq) : s.LocallyAsymptoticallyStable x_eq :=
  ⟨h.1, fun t₀ ht₀ => ⟨1, one_pos,
    fun t₁ x ht hx _ => (h.2 t₀ ht₀).1 t₁ x ht hx (mem_univ _),
    fun x hx _ => (h.2 t₀ ht₀).2 x hx⟩⟩

/-- A uniform convergence time gives convergence of every trajectory on a ray: past `t₀ + T(η)`
the trajectory stays within `η`, on every segment and so on the ray. -/
lemma HasUniformConvergenceTime.tendsto {c : ℝ} (h : s.HasUniformConvergenceTime x_eq c)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {x : ℝ → E} (hx : s.IsTrajectoryOn (fun _ => ()) x (Ici t₀))
    (hx₀ : ‖x t₀ - x_eq‖ < c) : Tendsto x atTop (𝓝 x_eq) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro η hη
  obtain ⟨T, -, hT⟩ := h η hη
  refine ⟨t₀ + T, fun t ht => ?_⟩
  -- restrict the ray trajectory to the segment `[t₀, t]`
  have h_seg : s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t) :=
    IsIntegralCurveOn.mono hx Icc_subset_Ici_self
  have h_near := hT t₀ ht₀ t x h_seg hx₀ t ⟨ht, le_rfl⟩
  rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]

/-- Uniform asymptotic stability implies local asymptotic stability, for a forward-complete
system.  Completeness is a genuine hypothesis: uniform asymptotic stability bounds every solution
segment but does not say that segments extend to `[t₀, ∞)`. -/
@[blueprint "lem:continuousSystem-uniformlyAsymptoticallyStable-local"
  (title := "Uniform asymptotic stability implies local asymptotic stability")
  (latexEnv := "lemma")
  (statement := /-- A uniformly asymptotically stable equilibrium
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}) of a forward-complete system
    (\cref{def:continuousSystem-isForwardComplete}) is locally asymptotically stable
    (\cref{def:continuousSystem-locallyAsymptoticallyStable}).  Forward completeness is needed:
    bounds on solution segments do not by themselves make the segments extend. -/)
  (proof := /-- Uniform stability gives stability; a uniform convergence time gives convergence
    of every trajectory on a ray, with the same radius $c$ for every $t_0$. -/)]
lemma UniformlyAsymptoticallyStable.locallyAsymptoticallyStable
    (h : s.UniformlyAsymptoticallyStable x_eq) (hfc : s.IsForwardComplete (fun _ => ())) :
    s.LocallyAsymptoticallyStable x_eq := by
  obtain ⟨h_us, c, hc, h_time⟩ := h
  exact ⟨h_us.stable, fun t₀ ht₀ => ⟨c, hc, fun t₁ x ht hx _ => hfc t₀ t₁ x ht hx (mem_univ _),
    fun x hx hx₀ => h_time.tendsto ht₀ hx hx₀⟩⟩

/-- Global uniform asymptotic stability implies uniform asymptotic stability. -/
lemma GloballyUniformlyAsymptoticallyStable.uniformlyAsymptoticallyStable
    (h : s.GloballyUniformlyAsymptoticallyStable x_eq) : s.UniformlyAsymptoticallyStable x_eq :=
  ⟨h.1.uniformlyStable, 1, one_pos, h.2 1 one_pos⟩

/-- Global uniform asymptotic stability implies global asymptotic stability, for a
forward-complete system. -/
@[blueprint "lem:continuousSystem-globallyUniformlyAsymptoticallyStable-global"
  (title := "Global uniform asymptotic stability implies global asymptotic stability")
  (latexEnv := "lemma")
  (statement := /-- A globally uniformly asymptotically stable equilibrium
    (\cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}) is globally
    asymptotically stable (\cref{def:continuousSystem-globallyAsymptoticallyStable}), given
    forward completeness (\cref{def:continuousSystem-isForwardComplete}). -/)
  (proof := /-- Every trajectory starts in some ball, and every ball has a uniform convergence
    time. -/)]
lemma GloballyUniformlyAsymptoticallyStable.globallyAsymptoticallyStable
    (h : s.GloballyUniformlyAsymptoticallyStable x_eq) (hfc : s.IsForwardComplete (fun _ => ())) :
    s.GloballyAsymptoticallyStable x_eq :=
  ⟨h.1.uniformlyStable.stable, fun t₀ ht₀ => ⟨hfc t₀, fun x hx =>
    (h.2 (‖x t₀ - x_eq‖ + 1) (by positivity)).tendsto ht₀ hx (lt_add_one _)⟩⟩

/-- An exponential estimate with constant `k` bounds every trajectory by `k` times its initial
distance, since `e^{-γ (t - t₀)} ≤ 1` for `t ≥ t₀`. -/
private lemma exp_bound_le {k γ t₀ t r : ℝ} (hk : 0 < k) (hγ : 0 < γ) (ht : t₀ ≤ t)
    (hr : 0 ≤ r) : k * r * Real.exp (-γ * (t - t₀)) ≤ k * r := by
  have h_exp : Real.exp (-γ * (t - t₀)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  calc k * r * Real.exp (-γ * (t - t₀)) ≤ k * r * 1 :=
        mul_le_mul_of_nonneg_left h_exp (by positivity)
    _ = k * r := mul_one _

/-- Local exponential stability implies uniform stability: take `δ = min c (ε / k)`. -/
@[blueprint "lem:continuousSystem-locallyExponentiallyStable-uniformlyStable"
  (title := "Exponential stability implies uniform stability")
  (latexEnv := "lemma")
  (statement := /-- A locally exponentially stable equilibrium
    (\cref{def:continuousSystem-locallyExponentiallyStable}) is uniformly stable
    (\cref{def:continuousSystem-uniformlyStable}). -/)
  (proof := /-- The estimate bounds the distance by $k$ times the initial distance, so
    $\delta = \min(c, \varepsilon / k)$ works for every $t_0$. -/)]
lemma LocallyExponentiallyStable.uniformlyStable (h : s.LocallyExponentiallyStable x_eq) :
    s.UniformlyStable x_eq := by
  obtain ⟨c, hc, k, hk, γ, hγ, h_est⟩ := h
  intro ε hε
  refine ⟨min c (ε / k), lt_min hc (div_pos hε hk), fun t₀ ht₀ t₁ x hx hx₀ t ht => ?_⟩
  -- the estimate bounds the distance by `k ‖x t₀ - x_eq‖ < k (ε / k) = ε`
  have hx₀_c : ‖x t₀ - x_eq‖ < c := hx₀.trans_le (min_le_left _ _)
  have hx₀_ε : k * ‖x t₀ - x_eq‖ < ε := by
    have := hx₀.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀' hk] at this
  calc ‖x t - x_eq‖ ≤ k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀)) :=
        h_est t₀ ht₀ t₁ x hx hx₀_c t ht
    _ ≤ k * ‖x t₀ - x_eq‖ := exp_bound_le hk hγ ht.1 (norm_nonneg _)
    _ < ε := hx₀_ε

/-- An exponential estimate from the ball of radius `c` gives a uniform convergence time from
that ball: after time `T` the distance is below `k c e^{-γ T}`, which is below any `η > 0` for `T`
large. -/
private lemma hasUniformConvergenceTime_of_exp_estimate {c k γ : ℝ} (hk : 0 < k) (hγ : 0 < γ)
    (h_est : ∀ t₀ : ℝ, 0 ≤ t₀ → ∀ (t₁ : ℝ) (x : ℝ → E),
      s.IsTrajectoryOn (fun _ => ()) x (Icc t₀ t₁) → ‖x t₀ - x_eq‖ < c →
        ∀ t ∈ Icc t₀ t₁, ‖x t - x_eq‖ ≤ k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀))) :
    s.HasUniformConvergenceTime x_eq c := by
  intro η hη
  -- a time `T > 0` with `k c e^{-γ T} < η`
  have h_decay : Tendsto (fun T : ℝ => k * c * Real.exp (-γ * T)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hγ)).const_mul (k * c)
    simpa [Function.comp_def, neg_mul] using this
  obtain ⟨T, hT, hT_pos⟩ := ((h_decay.eventually (gt_mem_nhds hη)).and
    (eventually_gt_atTop 0)).exists
  refine ⟨T, hT_pos, fun t₀ ht₀ t₁ x hx hx₀ t ht => ?_⟩
  have ht_seg : t ∈ Icc t₀ t₁ := ⟨by linarith [ht.1], ht.2⟩
  -- past `t₀ + T` the estimate is below `k c e^{-γ T} < η`
  have h_exp_mono : Real.exp (-γ * (t - t₀)) ≤ Real.exp (-γ * T) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.1])
  calc ‖x t - x_eq‖ ≤ k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀)) :=
        h_est t₀ ht₀ t₁ x hx hx₀ t ht_seg
    _ ≤ k * c * Real.exp (-γ * T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx₀.le hk.le) h_exp_mono (Real.exp_pos _).le
          (mul_nonneg hk.le ((norm_nonneg _).trans hx₀.le))
    _ < η := hT

/-- Local exponential stability implies uniform asymptotic stability: the exponential estimate
gives a uniform convergence time from the same ball. -/
@[blueprint "lem:continuousSystem-locallyExponentiallyStable-uniformlyAsymptoticallyStable"
  (title := "Exponential stability implies uniform asymptotic stability")
  (latexEnv := "lemma")
  (statement := /-- A locally exponentially stable equilibrium
    (\cref{def:continuousSystem-locallyExponentiallyStable}) is uniformly asymptotically stable
    (\cref{def:continuousSystem-uniformlyAsymptoticallyStable}). -/)
  (proof := /-- Uniform stability is
    \cref{lem:continuousSystem-locallyExponentiallyStable-uniformlyStable}.  From the ball of
    radius $c$ the distance after time $T$ is below $k c\, e^{-\gamma T}$, which is below any
    $\eta > 0$ for $T$ large, independently of $t_0$. -/)]
lemma LocallyExponentiallyStable.uniformlyAsymptoticallyStable
    (h : s.LocallyExponentiallyStable x_eq) : s.UniformlyAsymptoticallyStable x_eq := by
  obtain ⟨c, hc, k, hk, γ, hγ, h_est⟩ := h
  exact ⟨LocallyExponentiallyStable.uniformlyStable ⟨c, hc, k, hk, γ, hγ, h_est⟩, c, hc,
    hasUniformConvergenceTime_of_exp_estimate hk hγ h_est⟩

/-- Local exponential stability implies local asymptotic stability, for a forward-complete
system. -/
lemma LocallyExponentiallyStable.locallyAsymptoticallyStable
    (h : s.LocallyExponentiallyStable x_eq) (hfc : s.IsForwardComplete (fun _ => ())) :
    s.LocallyAsymptoticallyStable x_eq :=
  h.uniformlyAsymptoticallyStable.locallyAsymptoticallyStable hfc

/-- Global exponential stability implies local exponential stability, with any radius. -/
@[blueprint "lem:continuousSystem-globallyExponentiallyStable-local"
  (title := "Global exponential stability implies local exponential stability")
  (latexEnv := "lemma")
  (statement := /-- A globally exponentially stable equilibrium
    (\cref{def:continuousSystem-globallyExponentiallyStable}) is locally exponentially stable
    (\cref{def:continuousSystem-locallyExponentiallyStable}). -/)]
lemma GloballyExponentiallyStable.locallyExponentiallyStable
    (h : s.GloballyExponentiallyStable x_eq) : s.LocallyExponentiallyStable x_eq := by
  obtain ⟨k, hk, γ, hγ, h_est⟩ := h
  exact ⟨1, one_pos, k, hk, γ, hγ, fun t₀ ht₀ t₁ x hx _ => h_est t₀ ht₀ t₁ x hx⟩

/-- Global exponential stability implies global uniform asymptotic stability: `δ(ε) = ε / k`
grows without bound, and every ball has a uniform convergence time. -/
@[blueprint "lem:continuousSystem-globallyExponentiallyStable-globallyUniformlyAsymptoticallyStable"
  (title := "Global exponential stability implies global uniform asymptotic stability")
  (latexEnv := "lemma")
  (statement := /-- A globally exponentially stable equilibrium
    (\cref{def:continuousSystem-globallyExponentiallyStable}) is globally uniformly asymptotically
    stable (\cref{def:continuousSystem-globallyUniformlyAsymptoticallyStable}). -/)
  (proof := /-- The estimate bounds the distance by $k$ times the initial distance, so
    $\delta(\varepsilon) = \varepsilon / k$ witnesses global uniform stability.  For each radius
    $c$ the estimate is locally exponential from that ball, which gives a uniform convergence
    time by \cref{lem:continuousSystem-locallyExponentiallyStable-uniformlyAsymptoticallyStable}.
    -/)]
lemma GloballyExponentiallyStable.globallyUniformlyAsymptoticallyStable
    (h : s.GloballyExponentiallyStable x_eq) : s.GloballyUniformlyAsymptoticallyStable x_eq := by
  obtain ⟨k, hk, γ, hγ, h_est⟩ := h
  refine ⟨⟨fun ε => ε / k, fun ε hε => div_pos hε hk, tendsto_id.atTop_div_const hk,
    fun ε hε t₀ ht₀ t₁ x hx hx₀ t ht => ?_⟩, fun c hc => ?_⟩
  · -- global uniform stability with `δ(ε) = ε / k`
    have hx₀_ε : k * ‖x t₀ - x_eq‖ < ε := by rwa [lt_div_iff₀' hk] at hx₀
    calc ‖x t - x_eq‖ ≤ k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀)) :=
          h_est t₀ ht₀ t₁ x hx t ht
      _ ≤ k * ‖x t₀ - x_eq‖ := exp_bound_le hk hγ ht.1 (norm_nonneg _)
      _ < ε := hx₀_ε
  · -- from every ball the estimate gives a uniform convergence time
    exact hasUniformConvergenceTime_of_exp_estimate hk hγ fun t₀ ht₀ t₁ x hx _ =>
      h_est t₀ ht₀ t₁ x hx

/-- **Exponential stability pulls back along a semiconjugacy.**  Let a linear map `e : E → E'`
carry the field of `s`, centred at `x_eq`, into the field of `s'`, centred at `x_eq'`:
`F'(t, x_eq' + e(x - x_eq)) = e(F(t, x))`.  If `e` distorts norms by bounded factors, local
exponential stability of `x_eq'` for `s'` gives it for `x_eq` and `s`: trajectories of `s` are
carried to trajectories of `s'`. -/
@[blueprint "lem:continuousSystem-locallyExponentiallyStable-of-semiconj"
  (title := "Exponential stability under a change of coordinates")
  (latexEnv := "lemma")
  (statement := /-- Let $e : E \to E'$ be continuous linear with $\|x\| \le a\|e x\|$ and
    $\|e x\| \le b\|x\|$, $a, b > 0$, and let
    $F'(t, x_{\mathrm{eq}}' + e(x - x_{\mathrm{eq}})) = e(F(t, x))$.  If $x_{\mathrm{eq}}'$ is
    locally exponentially stable for $s'$
    (\cref{def:continuousSystem-locallyExponentiallyStable}), so is $x_{\mathrm{eq}}$ for $s$. -/)
  (proof := /-- If $x$ is a trajectory of $s$, then $x_{\mathrm{eq}}' + e(x - x_{\mathrm{eq}})$
    is one of $s'$.  Its estimate, with radius $c / b$ and constant $abk$, is one for $x$. -/)]
lemma LocallyExponentiallyStable.of_semiconj {E' Y' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {s' : ContinuousSystem E' Unit Y'} {x_eq' : E'} (e : E →L[ℝ] E')
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h_lo : ∀ x, ‖x‖ ≤ a * ‖e x‖)
    (h_up : ∀ x, ‖e x‖ ≤ b * ‖x‖)
    (h_conj : ∀ t x, s'.F t (x_eq' + e (x - x_eq)) () = e (s.F t x ()))
    (h : s'.LocallyExponentiallyStable x_eq') : s.LocallyExponentiallyStable x_eq := by
  obtain ⟨c, hc, k, hk, γ, hγ, h_est⟩ := h
  refine ⟨c / b, div_pos hc hb, a * b * k, by positivity, γ, hγ,
    fun t₀ ht₀ t₁ x hx hx₀ t ht => ?_⟩
  -- The image `y = x_eq' + e(x - x_eq)` is a trajectory of `s'`.
  set y : ℝ → E' := fun τ => x_eq' + e (x τ - x_eq)
  have hy : s'.IsTrajectoryOn (fun _ => ()) y (Icc t₀ t₁) := fun τ hτ => by
    have h_deriv := (e.hasFDerivAt.comp_hasDerivWithinAt τ ((hx τ hτ).sub_const x_eq)).const_add
      x_eq'
    simp only [vectorField, y, h_conj]
    exact h_deriv
  have hy_sub : ∀ τ, y τ - x_eq' = e (x τ - x_eq) := fun τ => add_sub_cancel_left _ _
  have hy₀ : ‖y t₀ - x_eq'‖ < c :=
    calc ‖y t₀ - x_eq'‖
        ≤ b * ‖x t₀ - x_eq‖ := by rw [hy_sub]; exact h_up _
      _ < b * (c / b) := by gcongr
      _ = c := by field_simp
  calc ‖x t - x_eq‖
      ≤ a * ‖y t - x_eq'‖ := by rw [hy_sub]; exact h_lo _
    _ ≤ a * (k * ‖y t₀ - x_eq'‖ * Real.exp (-γ * (t - t₀))) :=
        mul_le_mul_of_nonneg_left (h_est t₀ ht₀ t₁ y hy hy₀ t ht) ha.le
    _ ≤ a * (k * (b * ‖x t₀ - x_eq‖) * Real.exp (-γ * (t - t₀))) := by
        rw [hy_sub]
        gcongr
        exact h_up _
    _ = a * b * k * ‖x t₀ - x_eq‖ * Real.exp (-γ * (t - t₀)) := by ring

end ContinuousSystem
