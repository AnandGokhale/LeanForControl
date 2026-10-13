import LeanForControl.Systems.Discrete
import Mathlib.Analysis.SpecificLimits.Normed
import Architect

/-!
# `Stability.Discrete.Defs` — stability of discrete-time systems

Stability notions for an equilibrium `x_eq` of an autonomous (input-free) discrete-time system
`x⁺ = f(k, x)`, as a `DiscreteSystem E Unit Y`.  A system with input is unforced first, by
`DiscreteSystem.zeroInput`.

These are the notions of `Stability.Continuous.Defs`, under the same names in the namespace
`DiscreteSystem`: one definition per notion, for time-varying systems, with the initial time `k₀`
explicit.  A time-invariant system is a special case.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definitions 4.4–4.6, read in discrete time;
Jungers and van de Wouw, *Discrete-time nonlinear control systems*, Encyclopedia of Systems and
Control Engineering (2026), Definitions 2 and 3, which state the time-invariant case.

## Which trajectories are quantified over

Every notion quantifies over trajectories on rays `[k₀, ∞)`.  In continuous time that would
silently exclude solutions escaping in finite time, which is why `Stability.Continuous.Defs` uses
segments for bounds and asks for forward completeness alongside limits.  In discrete time there is
nothing to exclude: the recursion defines a trajectory from every initial time and state for all
later times (`DiscreteSystem.exists_isTrajectoryOn`), and it is unique
(`DiscreteSystem.IsTrajectoryOn.eq`).  So the ray is the whole story, and no forward-completeness
condition appears.

## Conventions

* Inequalities are strict, as in `Stability.Continuous.Defs`; Jungers and van de Wouw use
  non-strict ones, which define the same notions.
* The exponential estimate is geometric, `‖x(k) - x_eq‖ ≤ C ‖x(k₀) - x_eq‖ ρ^{k-k₀}` with
  `0 ≤ ρ < 1`; `ρ = e^{-γ}` recovers the continuous-time form.
* The equilibrium is a general `x_eq`; the references place it at the origin.
* The output space `Y` plays no role.
-/

open Set Filter Topology

namespace DiscreteSystem

variable {E Y : Type*} [NormedAddCommGroup E]

/-! ## Stability and instability -/

/-- The equilibrium `x_eq` is **stable**: for every `ε > 0` and initial time `k₀` there is
`δ > 0` such that every trajectory starting within `δ` of `x_eq` at `k₀` stays within `ε` of it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4; Jungers and van de Wouw (2026),
Definition 2 (*stability*). -/
@[blueprint "def:discreteSystem-stable"
  (title := "Stability of a discrete-time system")
  (statement := /-- The equilibrium $x_{\mathrm{eq}}$ of an autonomous discrete-time system
    $x^{+} = f(k, x)$ is \emph{stable} when for every $\varepsilon > 0$ and $k_0 \in \mathbb{N}$
    there is $\delta = \delta(\varepsilon, k_0) > 0$ such that every trajectory on
    $[k_0, \infty)$ with $\|x(k_0) - x_{\mathrm{eq}}\| < \delta$ satisfies
    $\|x(k) - x_{\mathrm{eq}}\| < \varepsilon$ for all $k \ge k_0$.

    The counterpart of \cref{def:continuousSystem-stable}.  Trajectories on rays suffice: a
    discrete-time trajectory exists from every state for all later times
    (\cref{lem:discreteSystem-exists-isTrajectoryOn}).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.4; Jungers and van de
    Wouw (2026), Definition 2. -/)]
def Stable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  ∀ ε > 0, ∀ k₀ : ℕ, ∃ δ > 0, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_eq‖ < δ →
      ∀ k ≥ k₀, ‖x k - x_eq‖ < ε

/-- The equilibrium `x_eq` is **unstable** when it is not stable. -/
@[blueprint "def:discreteSystem-unstable"
  (title := "Instability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{unstable} when it is not stable
    (\cref{def:discreteSystem-stable}). -/)]
def Unstable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  ¬ s.Stable x_eq

/-- The equilibrium `x_eq` is **uniformly stable**: `δ` in `Stable` can be chosen independently
of the initial time. -/
@[blueprint "def:discreteSystem-uniformlyStable"
  (title := "Uniform stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{uniformly stable} when $\delta$ in
    \cref{def:discreteSystem-stable} can be chosen independently of $k_0$. -/)]
def UniformlyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ k₀ : ℕ, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_eq‖ < δ →
      ∀ k ≥ k₀, ‖x k - x_eq‖ < ε

/-- The equilibrium `x_eq` is **globally uniformly stable**: uniformly stable, with a choice of
`δ(ε)` that grows without bound. -/
@[blueprint "def:discreteSystem-globallyUniformlyStable"
  (title := "Global uniform stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{globally uniformly stable} when it is uniformly stable
    (\cref{def:discreteSystem-uniformlyStable}) with a choice of $\delta(\varepsilon)$ satisfying
    $\delta(\varepsilon) \to \infty$ as $\varepsilon \to \infty$. -/)]
def GloballyUniformlyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  ∃ δ : ℝ → ℝ, (∀ ε > 0, 0 < δ ε) ∧ Tendsto δ atTop atTop ∧
    ∀ ε > 0, ∀ k₀ : ℕ, ∀ x : ℕ → E,
      s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_eq‖ < δ ε →
        ∀ k ≥ k₀, ‖x k - x_eq‖ < ε

/-! ## Asymptotic stability -/

/-- The equilibrium `x_eq` is **locally asymptotically stable**: stable, and for every initial
time `k₀` there is `c > 0` such that trajectories starting within `c` of `x_eq` converge to it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.4; Jungers and van de Wouw (2026),
Definition 2 (*asymptotic stability*). -/
@[blueprint "def:discreteSystem-locallyAsymptoticallyStable"
  (title := "Local asymptotic stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{locally asymptotically stable} when it is stable
    (\cref{def:discreteSystem-stable}) and for every $k_0$ there is $c = c(k_0) > 0$ such that
    every trajectory on $[k_0, \infty)$ with $\|x(k_0) - x_{\mathrm{eq}}\| < c$ satisfies
    $x(k) \to x_{\mathrm{eq}}$.  Unlike \cref{def:continuousSystem-locallyAsymptoticallyStable}
    no forward completeness is asked for: discrete-time trajectories always exist. -/)]
def LocallyAsymptoticallyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  s.Stable x_eq ∧ ∀ k₀ : ℕ, ∃ c > 0, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_eq‖ < c → Tendsto x atTop (𝓝 x_eq)

/-- The equilibrium `x_eq` is **globally asymptotically stable**: stable, and every trajectory
converges to it. -/
@[blueprint "def:discreteSystem-globallyAsymptoticallyStable"
  (title := "Global asymptotic stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{globally asymptotically stable} when it is stable
    (\cref{def:discreteSystem-stable}) and every trajectory on $[k_0, \infty)$ satisfies
    $x(k) \to x_{\mathrm{eq}}$. -/)]
def GloballyAsymptoticallyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  s.Stable x_eq ∧ ∀ k₀ : ℕ, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → Tendsto x atTop (𝓝 x_eq)

/-- Trajectories starting within `c` of `x_eq` are within any `η > 0` of it after a number of
steps `T(η)` that depends neither on the initial time nor on the trajectory. -/
@[blueprint "def:discreteSystem-hasUniformConvergenceTime"
  (title := "Uniform convergence time, discrete time")
  (statement := /-- Trajectories starting within $c$ of $x_{\mathrm{eq}}$ have a \emph{uniform
    convergence time}: for every $\eta > 0$ there is $T = T(\eta) \in \mathbb{N}$ such that every
    trajectory on $[k_0, \infty)$ with $\|x(k_0) - x_{\mathrm{eq}}\| < c$ satisfies
    $\|x(k) - x_{\mathrm{eq}}\| < \eta$ for $k \ge k_0 + T$. -/)]
def HasUniformConvergenceTime (s : DiscreteSystem E Unit Y) (x_eq : E) (c : ℝ) : Prop :=
  ∀ η > 0, ∃ T : ℕ, ∀ k₀ : ℕ, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_eq‖ < c →
      ∀ k ≥ k₀ + T, ‖x k - x_eq‖ < η

/-- The equilibrium `x_eq` is **uniformly asymptotically stable**: uniformly stable, with a
uniform convergence time from some ball around it. -/
@[blueprint "def:discreteSystem-uniformlyAsymptoticallyStable"
  (title := "Uniform asymptotic stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{uniformly asymptotically stable} when it is uniformly
    stable (\cref{def:discreteSystem-uniformlyStable}) and there is $c > 0$ from which convergence
    has a uniform convergence time (\cref{def:discreteSystem-hasUniformConvergenceTime}). -/)]
def UniformlyAsymptoticallyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  s.UniformlyStable x_eq ∧ ∃ c > 0, s.HasUniformConvergenceTime x_eq c

/-- The equilibrium `x_eq` is **globally uniformly asymptotically stable**: globally uniformly
stable, with a uniform convergence time from every ball around it. -/
@[blueprint "def:discreteSystem-globallyUniformlyAsymptoticallyStable"
  (title := "Global uniform asymptotic stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{globally uniformly asymptotically stable} when it is
    globally uniformly stable (\cref{def:discreteSystem-globallyUniformlyStable}) and every
    $c > 0$ admits a uniform convergence time
    (\cref{def:discreteSystem-hasUniformConvergenceTime}). -/)]
def GloballyUniformlyAsymptoticallyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  s.GloballyUniformlyStable x_eq ∧ ∀ c > 0, s.HasUniformConvergenceTime x_eq c

/-! ## Exponential stability -/

/-- The equilibrium `x_eq` is **locally exponentially stable** (geometrically stable): there are
`c, C > 0` and `0 ≤ ρ < 1` such that every trajectory starting within `c` of `x_eq` satisfies
`‖x(k) - x_eq‖ ≤ C ‖x(k₀) - x_eq‖ ρ^{k-k₀}`.  The constants do not depend on `k₀`.

Reference: Jungers and van de Wouw (2026), Definition 2 (*exponential stability or geometric
stability*), estimate (6). -/
@[blueprint "def:discreteSystem-locallyExponentiallyStable"
  (title := "Local exponential stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{locally exponentially stable}, or \emph{geometrically
    stable}, when there are $c, C > 0$ and $0 \le \rho < 1$ such that every trajectory on
    $[k_0, \infty)$ with $\|x(k_0) - x_{\mathrm{eq}}\| < c$ satisfies
    \[
      \|x(k) - x_{\mathrm{eq}}\| \le C\,\|x(k_0) - x_{\mathrm{eq}}\|\,\rho^{k - k_0}
      \qquad \forall\, k \ge k_0.
    \]
    The counterpart of \cref{def:continuousSystem-locallyExponentiallyStable}, with
    $\rho = e^{-\gamma}$.

    Reference: Jungers and van de Wouw (2026), Definition 2, estimate (6). -/)]
def LocallyExponentiallyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  ∃ c > 0, ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k₀ : ℕ, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_eq‖ < c →
      ∀ k ≥ k₀, ‖x k - x_eq‖ ≤ C * ‖x k₀ - x_eq‖ * ρ ^ (k - k₀)

/-- The equilibrium `x_eq` is **globally exponentially stable**: the geometric estimate holds for
every initial state. -/
@[blueprint "def:discreteSystem-globallyExponentiallyStable"
  (title := "Global exponential stability of a discrete-time system")
  (statement := /-- The equilibrium is \emph{globally exponentially stable} when the estimate of
    \cref{def:discreteSystem-locallyExponentiallyStable} holds for every initial state, with no
    radius $c$. -/)]
def GloballyExponentiallyStable (s : DiscreteSystem E Unit Y) (x_eq : E) : Prop :=
  ∃ C > 0, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k₀ : ℕ, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) →
      ∀ k ≥ k₀, ‖x k - x_eq‖ ≤ C * ‖x k₀ - x_eq‖ * ρ ^ (k - k₀)

/-! ## Ultimate boundedness -/

/-- Trajectories are **uniformly ultimately bounded** with ultimate bound `b` around `x_c`: there
is `c > 0` such that for every `a < c` a number of steps `T(a, b)` brings every trajectory
starting within `a` of `x_c` to within `b` of it.  A property of the system rather than of an
equilibrium: `x_c` need not be one.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.6; Jungers and van de Wouw (2026),
Definition 3, for a time-invariant system. -/
@[blueprint "def:discreteSystem-uniformlyUltimatelyBounded"
  (title := "Uniform ultimate boundedness of a discrete-time system")
  (statement := /-- Trajectories are \emph{uniformly ultimately bounded} with ultimate bound $b$
    around $x_c$ when there is $c > 0$ such that for every $0 < a < c$ there is
    $T = T(a, b) \in \mathbb{N}$ with
    \[
      \|x(k_0) - x_c\| \le a \;\Rightarrow\; \|x(k) - x_c\| \le b \qquad \forall\, k \ge k_0 + T
    \]
    for every trajectory on $[k_0, \infty)$.  The point $x_c$ need not be an equilibrium.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.6; Jungers and van de
    Wouw (2026), Definition 3. -/)]
def UniformlyUltimatelyBounded (s : DiscreteSystem E Unit Y) (x_c : E) (b : ℝ) : Prop :=
  ∃ c > 0, ∀ a, 0 < a → a < c → ∃ T : ℕ, ∀ k₀ : ℕ, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_c‖ ≤ a →
      ∀ k ≥ k₀ + T, ‖x k - x_c‖ ≤ b

/-- Trajectories are **globally uniformly ultimately bounded** with ultimate bound `b` around
`x_c`: `UniformlyUltimatelyBounded` for every initial radius `a`. -/
@[blueprint "def:discreteSystem-globallyUniformlyUltimatelyBounded"
  (title := "Global uniform ultimate boundedness of a discrete-time system")
  (statement := /-- Trajectories are \emph{globally uniformly ultimately bounded} with ultimate
    bound $b$ around $x_c$ when \cref{def:discreteSystem-uniformlyUltimatelyBounded} holds for
    every $a > 0$, with no radius $c$. -/)]
def GloballyUniformlyUltimatelyBounded (s : DiscreteSystem E Unit Y) (x_c : E) (b : ℝ) : Prop :=
  ∀ a > 0, ∃ T : ℕ, ∀ k₀ : ℕ, ∀ x : ℕ → E,
    s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_c‖ ≤ a →
      ∀ k ≥ k₀ + T, ‖x k - x_c‖ ≤ b

/-! ## Implications between the notions -/

variable {s : DiscreteSystem E Unit Y} {x_eq : E}

/-- **A stable equilibrium is a fixed point** of every step map: the trajectory from `x_eq` at
time `k` stays within every `ε` of `x_eq`, so its first step lands on `x_eq`. -/
@[blueprint "lem:discreteSystem-stable-isFixedPt"
  (title := "A stable equilibrium is a fixed point")
  (latexEnv := "lemma")
  (statement := /-- If $x_{\mathrm{eq}}$ is stable (\cref{def:discreteSystem-stable}), then
    $f(k, x_{\mathrm{eq}}) = x_{\mathrm{eq}}$ for every $k$. -/)
  (proof := /-- The trajectory from $x_{\mathrm{eq}}$ at time $k$ stays within every
    $\varepsilon > 0$ of $x_{\mathrm{eq}}$, so its value at $k + 1$, which is
    $f(k, x_{\mathrm{eq}})$, is at distance $0$. -/)]
lemma Stable.isFixedPt (h : s.Stable x_eq) (k : ℕ) : s.F k x_eq () = x_eq := by
  obtain ⟨x, hx, hx₀⟩ := s.exists_isTrajectoryOn (fun _ => ()) k x_eq
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨δ, hδ, h_bound⟩ := h ε hε k
  have h_near := h_bound x hx (by simpa [hx₀] using hδ) (k + 1) (Nat.le_succ k)
  rw [hx k self_mem_Ici, hx₀] at h_near
  rw [dist_eq_norm]
  exact h_near.le

/-- **Instability from a fixed escape radius.**  If for every `δ > 0` some trajectory starting
within `δ` of `x_eq` reaches distance `ε`, then `x_eq` is unstable. -/
@[blueprint "lem:discreteSystem-unstable-of-escape"
  (title := "Instability from a fixed escape radius, discrete time")
  (latexEnv := "lemma")
  (statement := /-- Fix $\varepsilon > 0$ and $k_0$.  If for every $\delta > 0$ some trajectory on
    $[k_0, \infty)$ starts within $\delta$ of $x_{\mathrm{eq}}$ and reaches distance at least
    $\varepsilon$ from it, then $x_{\mathrm{eq}}$ is unstable
    (\cref{def:discreteSystem-unstable}). -/)]
lemma unstable_of_escape {ε : ℝ} (hε : 0 < ε) (k₀ : ℕ)
    (hescape : ∀ δ > 0, ∃ (x : ℕ → E) (k : ℕ),
      s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) ∧ ‖x k₀ - x_eq‖ < δ ∧ k₀ ≤ k ∧
        ε ≤ ‖x k - x_eq‖) :
    s.Unstable x_eq := by
  intro h
  obtain ⟨δ, hδ, h_bound⟩ := h ε hε k₀
  obtain ⟨x, k, hx, hx₀, hk, h_far⟩ := hescape δ hδ
  exact h_far.not_gt (h_bound x hx hx₀ k hk)

/-- Uniform stability implies stability. -/
@[blueprint "lem:discreteSystem-uniformlyStable-stable"
  (title := "Uniform stability implies stability, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A uniformly stable equilibrium (\cref{def:discreteSystem-uniformlyStable}) is
    stable (\cref{def:discreteSystem-stable}). -/)]
lemma UniformlyStable.stable (h : s.UniformlyStable x_eq) : s.Stable x_eq := fun ε hε k₀ => by
  obtain ⟨δ, hδ, h_bound⟩ := h ε hε
  exact ⟨δ, hδ, h_bound k₀⟩

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
@[blueprint "lem:discreteSystem-globallyAsymptoticallyStable-local"
  (title := "Global asymptotic stability implies local, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A globally asymptotically stable equilibrium
    (\cref{def:discreteSystem-globallyAsymptoticallyStable}) is locally asymptotically stable
    (\cref{def:discreteSystem-locallyAsymptoticallyStable}). -/)]
lemma GloballyAsymptoticallyStable.locallyAsymptoticallyStable
    (h : s.GloballyAsymptoticallyStable x_eq) : s.LocallyAsymptoticallyStable x_eq :=
  ⟨h.1, fun k₀ => ⟨1, one_pos, fun x hx _ => h.2 k₀ x hx⟩⟩

/-- A uniform convergence time gives convergence of every trajectory starting in the ball. -/
lemma HasUniformConvergenceTime.tendsto {c : ℝ} (h : s.HasUniformConvergenceTime x_eq c)
    {k₀ : ℕ} {x : ℕ → E} (hx : s.IsTrajectoryOn (fun _ => ()) x (Ici k₀))
    (hx₀ : ‖x k₀ - x_eq‖ < c) : Tendsto x atTop (𝓝 x_eq) := by
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro η hη
  obtain ⟨T, hT⟩ := h η hη
  exact ⟨k₀ + T, fun k hk => by simpa using hT k₀ x hx hx₀ k hk⟩

/-- Uniform asymptotic stability implies local asymptotic stability.  Unlike continuous time no
forward completeness is needed. -/
@[blueprint "lem:discreteSystem-uniformlyAsymptoticallyStable-local"
  (title := "Uniform asymptotic stability implies local, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A uniformly asymptotically stable equilibrium
    (\cref{def:discreteSystem-uniformlyAsymptoticallyStable}) is locally asymptotically stable
    (\cref{def:discreteSystem-locallyAsymptoticallyStable}).  Unlike
    \cref{lem:continuousSystem-uniformlyAsymptoticallyStable-local}, no forward completeness is
    needed. -/)]
lemma UniformlyAsymptoticallyStable.locallyAsymptoticallyStable
    (h : s.UniformlyAsymptoticallyStable x_eq) : s.LocallyAsymptoticallyStable x_eq := by
  obtain ⟨h_us, c, hc, h_time⟩ := h
  exact ⟨h_us.stable, fun _ => ⟨c, hc, fun _ hx hx₀ => h_time.tendsto hx hx₀⟩⟩

/-- Global uniform asymptotic stability implies uniform asymptotic stability. -/
lemma GloballyUniformlyAsymptoticallyStable.uniformlyAsymptoticallyStable
    (h : s.GloballyUniformlyAsymptoticallyStable x_eq) : s.UniformlyAsymptoticallyStable x_eq :=
  ⟨h.1.uniformlyStable, 1, one_pos, h.2 1 one_pos⟩

/-- Global uniform asymptotic stability implies global asymptotic stability. -/
@[blueprint "lem:discreteSystem-globallyUniformlyAsymptoticallyStable-global"
  (title := "Global uniform asymptotic stability implies global, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A globally uniformly asymptotically stable equilibrium
    (\cref{def:discreteSystem-globallyUniformlyAsymptoticallyStable}) is globally asymptotically
    stable (\cref{def:discreteSystem-globallyAsymptoticallyStable}). -/)]
lemma GloballyUniformlyAsymptoticallyStable.globallyAsymptoticallyStable
    (h : s.GloballyUniformlyAsymptoticallyStable x_eq) : s.GloballyAsymptoticallyStable x_eq :=
  ⟨h.1.uniformlyStable.stable, fun k₀ x hx =>
    (h.2 (‖x k₀ - x_eq‖ + 1) (by positivity)).tendsto hx (lt_add_one _)⟩

/-- A geometric estimate with constant `C` bounds every trajectory by `C` times its initial
distance, since `ρ^n ≤ 1`. -/
private lemma geom_bound_le {C ρ r : ℝ} (hC : 0 < C) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (hr : 0 ≤ r)
    (n : ℕ) : C * r * ρ ^ n ≤ C * r :=
  mul_le_of_le_one_right (by positivity) (pow_le_one₀ hρ₀ hρ₁.le)

/-- Local exponential stability implies uniform stability: take `δ = min c (ε / C)`. -/
@[blueprint "lem:discreteSystem-locallyExponentiallyStable-uniformlyStable"
  (title := "Exponential stability implies uniform stability, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A locally exponentially stable equilibrium
    (\cref{def:discreteSystem-locallyExponentiallyStable}) is uniformly stable
    (\cref{def:discreteSystem-uniformlyStable}). -/)
  (proof := /-- The estimate bounds the distance by $C$ times the initial distance, so
    $\delta = \min(c, \varepsilon / C)$ works for every $k_0$. -/)]
lemma LocallyExponentiallyStable.uniformlyStable (h : s.LocallyExponentiallyStable x_eq) :
    s.UniformlyStable x_eq := by
  obtain ⟨c, hc, C, hC, ρ, hρ₀, hρ₁, h_est⟩ := h
  intro ε hε
  refine ⟨min c (ε / C), lt_min hc (div_pos hε hC), fun k₀ x hx hx₀ k hk => ?_⟩
  have hx₀_ε : C * ‖x k₀ - x_eq‖ < ε := by
    have := hx₀.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀' hC] at this
  calc ‖x k - x_eq‖ ≤ C * ‖x k₀ - x_eq‖ * ρ ^ (k - k₀) :=
        h_est k₀ x hx (hx₀.trans_le (min_le_left _ _)) k hk
    _ ≤ C * ‖x k₀ - x_eq‖ := geom_bound_le hC hρ₀ hρ₁ (norm_nonneg _) _
    _ < ε := hx₀_ε

/-- A geometric estimate from the ball of radius `c` gives a uniform convergence time from that
ball: after `T` steps the distance is below `C c ρ^T`, which is below any `η > 0` for `T` large. -/
private lemma hasUniformConvergenceTime_of_geom_estimate {c C ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (h_est : ∀ k₀ : ℕ, ∀ x : ℕ → E,
      s.IsTrajectoryOn (fun _ => ()) x (Ici k₀) → ‖x k₀ - x_eq‖ < c →
        ∀ k ≥ k₀, ‖x k - x_eq‖ ≤ C * ‖x k₀ - x_eq‖ * ρ ^ (k - k₀)) (hC : 0 < C) :
    s.HasUniformConvergenceTime x_eq c := by
  intro η hη
  have h_decay : Tendsto (fun T : ℕ => C * c * ρ ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀ hρ₁).const_mul (C * c)
  obtain ⟨T, hT⟩ := (h_decay.eventually (gt_mem_nhds hη)).exists
  refine ⟨T, fun k₀ x hx hx₀ k hk => ?_⟩
  calc ‖x k - x_eq‖ ≤ C * ‖x k₀ - x_eq‖ * ρ ^ (k - k₀) := h_est k₀ x hx hx₀ k (by omega)
    _ ≤ C * c * ρ ^ T :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx₀.le hC.le)
          (pow_le_pow_of_le_one hρ₀ hρ₁.le (by omega)) (by positivity)
          (mul_nonneg hC.le ((norm_nonneg _).trans hx₀.le))
    _ < η := hT

/-- Local exponential stability implies uniform asymptotic stability. -/
@[blueprint "lem:discreteSystem-locallyExponentiallyStable-uniformlyAsymptoticallyStable"
  (title := "Exponential stability implies uniform asymptotic stability, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A locally exponentially stable equilibrium
    (\cref{def:discreteSystem-locallyExponentiallyStable}) is uniformly asymptotically stable
    (\cref{def:discreteSystem-uniformlyAsymptoticallyStable}). -/)
  (proof := /-- Uniform stability is
    \cref{lem:discreteSystem-locallyExponentiallyStable-uniformlyStable}.  From the ball of
    radius $c$ the distance after $T$ steps is below $C c \rho^{T}$, which is below any
    $\eta > 0$ for $T$ large, independently of $k_0$. -/)]
lemma LocallyExponentiallyStable.uniformlyAsymptoticallyStable
    (h : s.LocallyExponentiallyStable x_eq) : s.UniformlyAsymptoticallyStable x_eq := by
  obtain ⟨c, hc, C, hC, ρ, hρ₀, hρ₁, h_est⟩ := h
  exact ⟨LocallyExponentiallyStable.uniformlyStable ⟨c, hc, C, hC, ρ, hρ₀, hρ₁, h_est⟩, c, hc,
    hasUniformConvergenceTime_of_geom_estimate hρ₀ hρ₁ h_est hC⟩

/-- Local exponential stability implies local asymptotic stability. -/
lemma LocallyExponentiallyStable.locallyAsymptoticallyStable
    (h : s.LocallyExponentiallyStable x_eq) : s.LocallyAsymptoticallyStable x_eq :=
  h.uniformlyAsymptoticallyStable.locallyAsymptoticallyStable

/-- Global exponential stability implies local exponential stability, with any radius. -/
@[blueprint "lem:discreteSystem-globallyExponentiallyStable-local"
  (title := "Global exponential stability implies local, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A globally exponentially stable equilibrium
    (\cref{def:discreteSystem-globallyExponentiallyStable}) is locally exponentially stable
    (\cref{def:discreteSystem-locallyExponentiallyStable}). -/)]
lemma GloballyExponentiallyStable.locallyExponentiallyStable
    (h : s.GloballyExponentiallyStable x_eq) : s.LocallyExponentiallyStable x_eq := by
  obtain ⟨C, hC, ρ, hρ₀, hρ₁, h_est⟩ := h
  exact ⟨1, one_pos, C, hC, ρ, hρ₀, hρ₁, fun k₀ x hx _ => h_est k₀ x hx⟩

/-- Global exponential stability implies global uniform asymptotic stability. -/
@[blueprint "lem:discreteSystem-globallyExponentiallyStable-globallyUniformlyAsymptoticallyStable"
  (title := "Global exponential stability implies global uniform, discrete time")
  (latexEnv := "lemma")
  (statement := /-- A globally exponentially stable equilibrium
    (\cref{def:discreteSystem-globallyExponentiallyStable}) is globally uniformly asymptotically
    stable (\cref{def:discreteSystem-globallyUniformlyAsymptoticallyStable}). -/)
  (proof := /-- $\delta(\varepsilon) = \varepsilon / C$ witnesses global uniform stability, and
    from every ball the estimate gives a uniform convergence time as in
    \cref{lem:discreteSystem-locallyExponentiallyStable-uniformlyAsymptoticallyStable}. -/)]
lemma GloballyExponentiallyStable.globallyUniformlyAsymptoticallyStable
    (h : s.GloballyExponentiallyStable x_eq) : s.GloballyUniformlyAsymptoticallyStable x_eq := by
  obtain ⟨C, hC, ρ, hρ₀, hρ₁, h_est⟩ := h
  refine ⟨⟨fun ε => ε / C, fun ε hε => div_pos hε hC, tendsto_id.atTop_div_const hC,
    fun ε hε k₀ x hx hx₀ k hk => ?_⟩, fun c _ => ?_⟩
  · have hx₀_ε : C * ‖x k₀ - x_eq‖ < ε := by rwa [lt_div_iff₀' hC] at hx₀
    calc ‖x k - x_eq‖ ≤ C * ‖x k₀ - x_eq‖ * ρ ^ (k - k₀) := h_est k₀ x hx k hk
      _ ≤ C * ‖x k₀ - x_eq‖ := geom_bound_le hC hρ₀ hρ₁ (norm_nonneg _) _
      _ < ε := hx₀_ε
  · exact hasUniformConvergenceTime_of_geom_estimate hρ₀ hρ₁
      (fun k₀ x hx _ => h_est k₀ x hx) hC

end DiscreteSystem
