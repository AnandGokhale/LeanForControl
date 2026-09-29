import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.MonotoneContinuity
import Architect

variable {n : ℕ}

/-!
# `Stability.DefsAutonomous`

Core definitions for the stability theory of autonomous ODEs `ẋ = f(x)` on `ℝⁿ`.

## Notation

`ℝⁿ` denotes `EuclideanSpace ℝ (Fin n)` throughout this file and all files that import it.

## Contents

* **Solution segments and equilibria** (`IsTrajectoryOn`, `IsEquilibrium`).
* **Stability predicates** (`LyapunovStable`, `LocalAsymptoticStable`,
  `GlobalAsymptoticStable`).
* **Sublevel sets** (`SublevelSet`).
* **Lyapunov function structures**, forming the hierarchy:
  - `IsLocalLyapunovFunction` → `LyapunovStable`
  - `IsStrictLocalLyapunovFunction` → `LocalAsymptoticStable`
  - `IsStrictLyapunovFunction` → `GlobalAsymptoticStable`
  - `IsAsymptoticLyapunovFunction` → `GlobalAsymptoticStable` (classical radially-unbounded form)
* **Positive invariance** (`IsPositivelyInvariant`).
* **Compact sublevel sets** (`isCompact_sublevel_set`).
-/

open Set Filter Topology

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-! ## System primitives -/

/-- `φ` solves `ẋ = f(x)` on the segment `[t₀, t₁]`.

Reducible, so it is the Mathlib notion rather than a wrapper around it: `hφ.continuousOn`,
`hφ.mono`, and direct application `hφ t ht` all work, and a bare `IsIntegralCurveOn` is
accepted wherever this is expected. -/
@[blueprint "def:isTrajectoryOn"
  (title := "Solution segment")
  (statement := /-- A \emph{solution segment} of $\dot{x} = f(x)$ on $[t_0, t_1]$ is an
    integral curve of the vector field restricted to that interval. Unlike a globally
    defined trajectory it need not exist for all time, so quantifying over segments
    does not silently discard solutions with a finite escape time. -/)]
abbrev IsTrajectoryOn (φ : ℝ → ℝⁿ) (f : ℝⁿ → ℝⁿ) (t₀ t₁ : ℝ) : Prop :=
  IsIntegralCurveOn φ (fun _ x => f x) (Icc t₀ t₁)

/-- An equilibrium point `x_eq` of `ẋ = f(x)`: `f(x_eq) = 0`. -/
@[blueprint "def:isEquilibrium"
  (title := "Equilibrium point")
  (statement := /-- A point $x_{\mathrm{eq}} \in \mathbb{R}^{n}$ is an
    \emph{equilibrium} of $\dot{x} = f(x)$ when $f(x_{\mathrm{eq}}) = 0$. -/)]
def IsEquilibrium (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  f x_eq = 0

/-! ## Stability predicates -/

/-- Lyapunov stability, quantified over all finite forward solution segments.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.1 (*stable*), for `ẋ = f(x)`.
Differences:
- Khalil fixes `t₀ = 0`; here it is arbitrary. Immaterial for an autonomous field.
- Khalil presumes solutions on `[0, ∞)`; here the quantification is over finite forward
  segments, so the predicate is not vacuous when solutions escape in finite time.
-/
@[blueprint "def:lyapunovStable"
  (title := "Lyapunov stability")
  (statement := /-- An equilibrium is Lyapunov stable when every finite
    forward solution segment starting sufficiently close remains within any
    prescribed neighborhood for its entire interval of definition.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.1 (\emph{stable}), for
    $\dot{x} = f(x)$.  Differences:
    \begin{itemize}
      \item Khalil fixes $t_0 = 0$; here it is arbitrary.  Immaterial for an autonomous field.
      \item Khalil presumes solutions on $[0,\infty)$; here the quantification is over finite
        forward segments, so the predicate is not vacuous when solutions escape in finite time.
    \end{itemize}
  -/)]
def LyapunovStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ),
    IsTrajectoryOn φ f t₀ t₁ → ‖φ t₀ - x_eq‖ < δ →
      ∀ t ∈ Icc t₀ t₁, ‖φ t - x_eq‖ < ε

/-- Local exponential stability on every finite forward solution segment.

The radius `r` selects the local basin; `C ≥ 1` is the overshoot constant and
`a > 0` is the exponential decay rate. Decay is measured from `t₀`, not from the
time origin.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:locallyExponentiallyStable"
  (title := "Local exponential stability")
  (statement := /-- An equilibrium is locally exponentially stable on finite
    forward segments when nearby solutions satisfy a uniform estimate
    $\|x(t)-x_{\rm eq}\|\leq C e^{-a(t-t_0)}\|x(t_0)-x_{\rm eq}\|$.

    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)]
def LocallyExponentiallyStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ∃ r C a : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < a ∧
    ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
      ‖φ t₀ - x_eq‖ < r → ∀ t ∈ Icc t₀ t₁,
        ‖φ t - x_eq‖ ≤ C * Real.exp (-a * (t - t₀)) * ‖φ t₀ - x_eq‖

/-- Local asymptotic stability: Lyapunov stable, and forward-complete solutions
starting within `c` converge to the equilibrium.

Attractivity is per-solution and quantifies over forward-complete solutions, as convergence must.
The completeness restriction is harmless because the stability conjunct guards it: where
solutions escape in finite time `LyapunovStable` already fails. A `τ` uniform over
solutions is strictly stronger and is recorded separately, for the certificates that supply it.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.1 (*asymptotically stable*), for
`ẋ = f(x)`. Differences:
- Khalil reuses the stability `δ` as the attractivity radius; here `c` is separate.
- Convergence is asserted only of forward-complete solutions.
-/
@[blueprint "def:localAsymptoticStable"
  (title := "Local asymptotic stability")
  (statement := /-- An equilibrium is \emph{locally asymptotically stable} when it is forward
    Lyapunov stable and there is a radius $c>0$ such that every solution defined for all
    forward time with $\|\varphi(t_0)-x_{\rm eq}\|<c$ satisfies
    $\varphi(t)\to x_{\rm eq}$ as $t\to\infty$.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.1
    (\emph{asymptotically stable}), for $\dot{x} = f(x)$.  Differences:
    \begin{itemize}
      \item Khalil reuses the stability $\delta$ as the attractivity radius; here $c$ is
        separate.
      \item Convergence is asserted only of forward-complete solutions.
    \end{itemize}
  -/)]
def LocalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∃ c > 0, ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ), IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀) →
    ‖φ t₀ - x_eq‖ < c → Tendsto φ atTop (𝓝 x_eq)

/-- Global asymptotic stability: Lyapunov stable, and *every* forward-complete solution
converges to the equilibrium.

As `LocalAsymptoticStable` but with no basin restriction.

Reference: Khalil, *Nonlinear Systems*.
-/
@[blueprint "def:globalAsymptoticStable"
  (title := "Global asymptotic stability")
  (statement := /-- An equilibrium is \emph{globally asymptotically stable} when it is forward
    Lyapunov stable and every solution defined for all forward time satisfies
    $\varphi(t)\to x_{\rm eq}$ as $t\to\infty$.

    Reference: Khalil, \emph{Nonlinear Systems}.
  -/)]
def GlobalAsymptoticStable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  LyapunovStable f x_eq ∧
  ∀ (t₀ : ℝ) (φ : ℝ → ℝⁿ), IsIntegralCurveOn φ (fun _ y => f y) (Ici t₀) →
    Tendsto φ atTop (𝓝 x_eq)

/-- Instability is the negation of forward Lyapunov stability.

Reference: Khalil, *Nonlinear Systems* (3rd ed.), Definition 4.1 (*unstable*), for `ẋ = f(x)`.
-/
@[blueprint "def:unstable"
  (title := "Instability")
  (statement := /-- Instability is the negation of stability quantified
    over all finite forward solution segments.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Definition 4.1 (\emph{unstable}), for
    $\dot{x} = f(x)$.
  -/)]
def Unstable (f : ℝⁿ → ℝⁿ) (x_eq : ℝⁿ) : Prop :=
  ¬ LyapunovStable f x_eq

/-! ## Sublevel sets -/

/-- The sublevel set `{x | V(x) ≤ c}` of `V` at level `c`. -/
@[blueprint "def:sublevelSet"
  (title := "Sublevel set")
  (statement := /-- The \emph{sublevel set} of $V : \mathbb{R}^{n} \to \mathbb{R}$
    at level $c \in \mathbb{R}$ is
    \[
      \Omega_{c}(V) \;=\; \{\, x \in \mathbb{R}^{n} \;:\; V(x) \le c \,\}.
    \] -/)]
def SublevelSet (V : ℝⁿ → ℝ) (c : ℝ) : Set ℝⁿ := {x | V x ≤ c}

/-! ## Lyapunov function structures

Four structures forming a hierarchy:

  IsLocalLyapunovFunction (on domain D) → LyapunovStable
  IsStrictLocalLyapunovFunction (on domain D, compact sublevel set) → LocalAsymptoticStable
  IsStrictLyapunovFunction (global, compact sublevel sets) → GlobalAsymptoticStable
  IsAsymptoticLyapunovFunction (global, radially unbounded) → GlobalAsymptoticStable

For the local structures, V : ℝⁿ → ℝ is globally continuous and differentiable
(needed for chain rule and IVT arguments), but positivity and Lie-derivative
conditions hold only on the domain D. The bridge lemma `contDiffOn_extension`
justifies this: any C¹ function on open D extends to a globally C¹ function
agreeing with the original on a neighborhood of x_eq.

The Lie derivative DV(x)[f(x)] = fderiv ℝ V x (f x). -/

/-- Local Lyapunov certificate: `V` is positive definite on `D` and has nonpositive Lie
    derivative on `D`. Implies `LyapunovStable`.

    `D` is an open neighborhood of `x_eq`; `V` is globally smooth so that the chain rule
    and IVT arguments can be applied uniformly. -/
@[blueprint "def:isLocalLyapunovFunction"
  (title := "Local Lyapunov function")
  (statement := /-- A function $V : \mathbb{R}^{n} \to \mathbb{R}$ is a
    \emph{local Lyapunov function} on an open domain $D \ni x_{\mathrm{eq}}$
    when $V$ is continuous and differentiable on all of $\mathbb{R}^n$,
    $V(x_{\mathrm{eq}}) = 0$, $V > 0$ on
    $D \setminus \{x_{\mathrm{eq}}\}$, and the Lie derivative satisfies
    $\dot{V}(x) = \nabla V(x) \cdot f(x) \le 0$ for all $x \in D$.

    Global regularity of $V$, with positivity and the Lie-derivative sign required only on
    $D$, is what lets the chain-rule and intermediate-value arguments be applied uniformly.
    Note this notion does \emph{not} require $x_{\mathrm{eq}}$ to be an equilibrium; the
    strict variants below do.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.1, hypotheses (4.2) and (4.3),
    for $\dot{x} = f(x)$.
  -/)]
structure IsLocalLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open     : IsOpen D
  hD_mem      : x_eq ∈ D
  hcont       : Continuous V
  hV_diff     : Differentiable ℝ V
  hzero       : V x_eq = 0
  hpos        : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hLie_nonpos : ∀ x ∈ D, fderiv ℝ V x (f x) ≤ 0

/-- Strict local Lyapunov certificate: `V` has strictly negative Lie derivative on `D`
    and a compact sublevel set `{V ≤ c} ⊆ D`. Implies `LocalAsymptoticStable`.

    `hcompact`: ∃ c > 0 with `{V ≤ c} ⊆ D` and `{V ≤ c}` compact. This replaces radial
    unboundedness and holds whenever `D` is bounded or `V` grows toward `∂D`. -/
@[blueprint "def:isStrictLocalLyapunovFunction"
  (title := "Strict local Lyapunov function")
  (statement := /-- A \emph{strict local Lyapunov function} on $D$ strengthens
    \cref{def:isLocalLyapunovFunction} in three ways: $V$ is required to be $C^{1}$ rather
    than merely differentiable; $x_{\mathrm{eq}}$ must be an equilibrium,
    $f(x_{\mathrm{eq}}) = 0$; and the Lie derivative is strictly negative,
    $\dot{V}(x) < 0$ for all $x \in D \setminus \{x_{\mathrm{eq}}\}$.  It additionally
    requires a $c > 0$ with $\Omega_{c}(V) \subseteq D$ compact
    (\cref{def:sublevelSet}), which replaces radial unboundedness in the local setting.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.1, hypotheses (4.2) and (4.4),
    for $\dot{x} = f(x)$.  The equilibrium and compact-sublevel-set fields are additional: Khalil
    obtains the compact set inside the proof, and leaves $f(x_{\mathrm{eq}}) = 0$ to the standing
    setup of (4.1).
  -/)]
structure IsStrictLocalLyapunovFunction
    (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) (D : Set ℝⁿ) : Prop where
  hD_open   : IsOpen D
  hD_mem    : x_eq ∈ D
  hcont     : Continuous V
  hV_c1     : ContDiff ℝ 1 V
  hzero     : V x_eq = 0
  hpos      : ∀ x ∈ D, x ≠ x_eq → 0 < V x
  hequil    : f x_eq = 0
  hLie_neg  : ∀ x ∈ D, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hcompact  : ∃ c > 0, SublevelSet V c ⊆ D ∧ IsCompact (SublevelSet V c)

/-- Global strict Lyapunov certificate: `V` is C¹, positive definite, with strictly negative Lie
    derivative on all of `ℝⁿ`, and all sublevel sets are compact (coercivity). Implies GAS.

    `hbounded_sublevel` encodes coercivity; in `ℝⁿ` this is equivalent to radial unboundedness.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.2, hypotheses (4.5) and (4.7),
    with (4.6) in its compact-sublevel-set form. -/
@[blueprint "def:isStrictLyapunovFunction"
  (title := "Strict Lyapunov function")
  (statement := /-- A \emph{global strict Lyapunov function} for $\dot{x} = f(x)$
    at $x_{\mathrm{eq}}$ is a $C^{1}$ map $V : \mathbb{R}^{n} \to \mathbb{R}$
    with $f(x_{\mathrm{eq}}) = 0$, $V(x_{\mathrm{eq}}) = 0$, $V > 0$ everywhere else,
    $\dot{V}(x) < 0$ on $\mathbb{R}^{n} \setminus \{x_{\mathrm{eq}}\}$,
    and all sublevel sets $\Omega_{c}(V)$ compact (coercivity).

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.2, hypotheses (4.5) and (4.7),
    for $\dot{x} = f(x)$.  Differences: \begin{itemize} \item Radial unboundedness (4.6) is replaced
    by compactness of every sublevel set, which for continuous $V$ it implies
    (\cref{lem:isCompact-sublevel-set}). \item The equilibrium field $f(x_{\mathrm{eq}}) = 0$ is
    additional. \end{itemize}
  -/)]
structure IsStrictLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont             : Continuous V
  hV_c1             : ContDiff ℝ 1 V
  hzero             : V x_eq = 0
  hpos              : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil            : f x_eq = 0
  hLie_neg          : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hbounded_sublevel : ∀ c : ℝ, IsCompact {x : ℝⁿ | V x ≤ c}

/-- Classical GAS Lyapunov certificate: C¹, positive definite, strictly negative Lie derivative,
    and radially unbounded (`V(x) → ∞` as `‖x‖ → ∞`). Implies `IsStrictLyapunovFunction`
    via `isCompact_sublevel_set` in `Autonomous.lean`.

    Reference: Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.2, hypotheses (4.5), (4.6),
    (4.7). -/
@[blueprint "def:isAsymptoticLyapunovFunction"
  (title := "Asymptotic Lyapunov function")
  (statement := /-- The classical GAS Lyapunov certificate: a $C^{1}$ map
    $V : \mathbb{R}^{n} \to \mathbb{R}$ with $f(x_{\mathrm{eq}}) = 0$,
    $V(x_{\mathrm{eq}}) = 0$,
    $V > 0$ elsewhere, $\dot{V} < 0$ on $\mathbb{R}^{n} \setminus \{x_{\mathrm{eq}}\}$,
    and radially unbounded ($V(x) \to \infty$ as $\|x\| \to \infty$).
    Implies \cref{def:isStrictLyapunovFunction} via
    \cref{lem:isCompact-sublevel-set}.

    Reference: Khalil, \emph{Nonlinear Systems} (3rd ed.), Theorem 4.2, hypotheses (4.5), (4.6) and
    (4.7), for $\dot{x} = f(x)$.  The equilibrium field $f(x_{\mathrm{eq}}) = 0$ is additional, left
    by Khalil to the standing setup of (4.1).
  -/)]
structure IsAsymptoticLyapunovFunction (f : ℝⁿ → ℝⁿ) (V : ℝⁿ → ℝ) (x_eq : ℝⁿ) : Prop where
  hcont    : Continuous V
  hV_c1    : ContDiff ℝ 1 V
  hzero    : V x_eq = 0
  hpos     : ∀ x : ℝⁿ, x ≠ x_eq → 0 < V x
  hequil   : f x_eq = 0
  hLie_neg : ∀ x : ℝⁿ, x ≠ x_eq → fderiv ℝ V x (f x) < 0
  hradial  : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop

/-! ## Positive invariance -/

/-- A set `S` is positively invariant for `ẋ = f(x)`: every solution segment starting in `S`
    remains in `S` for its whole interval of definition. -/
@[blueprint "def:isPositivelyInvariant"
  (title := "Positively invariant set")
  (statement := /-- A set $S \subseteq \mathbb{R}^{n}$ is \emph{positively invariant}
    for $\dot{x} = f(x)$ when every solution segment $\varphi$ on $[t_0, t_1]$ starting
    in $S$ remains in $S$ throughout:
    \[
      \varphi(t_0) \in S \;\Rightarrow\; \varphi(t) \in S
        \quad \forall\, t \in [t_0, t_1].
    \] -/)]
def IsPositivelyInvariant (S : Set ℝⁿ) (f : ℝⁿ → ℝⁿ) : Prop :=
  ∀ (t₀ t₁ : ℝ) (φ : ℝ → ℝⁿ), IsTrajectoryOn φ f t₀ t₁ →
    φ t₀ ∈ S → ∀ t ∈ Icc t₀ t₁, φ t ∈ S

/-- Sublevel sets of a radially unbounded continuous function are compact.

Proof:
1. Closed: `SublevelSet V c = V ⁻¹' (Iic c)`, closed by continuity.
2. Bounded: coercivity gives `R` with `SublevelSet V c ⊆ closedBall 0 R`.
3. Heine–Borel in `ℝⁿ`: closed + bounded = compact. -/
@[blueprint "lem:isCompact-sublevel-set"
  (title := "Sublevel sets of a radially unbounded function are compact")
  (latexEnv := "lemma")
  (statement := /-- If $V : \mathbb{R}^{n} \to \mathbb{R}$ is continuous and
    radially unbounded ($V(x) \to \infty$ as $\|x\| \to \infty$), then every
    sublevel set $\Omega_{c}(V)$ (\cref{def:sublevelSet}) is compact. -/)
  (proof := /-- Closed: $\Omega_{c}(V) = V^{-1}((-\infty,c])$ by continuity.
    Bounded: coercivity yields $R$ with $\Omega_{c}(V) \subseteq \overline{B}(0,R)$.
    Compact: Heine--Borel in $\mathbb{R}^{n}$. -/)]
lemma isCompact_sublevel_set
    (V : ℝⁿ → ℝ) (hcont : Continuous V)
    (hradial : Filter.Tendsto V (Filter.comap norm Filter.atTop) Filter.atTop)
    (c : ℝ) : IsCompact (SublevelSet V c) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_Iic.preimage hcont
  · rw [comap_norm_atTop, Metric.cobounded_eq_cocompact] at hradial
    have hev : {x : ℝⁿ | c < V x} ∈ Filter.cocompact ℝⁿ :=
      hradial (Filter.eventually_gt_atTop c)
    rw [Filter.mem_cocompact] at hev
    obtain ⟨K, hK_compact, hK⟩ := hev
    rw [Metric.isBounded_iff_subset_closedBall 0]
    obtain ⟨R, hR⟩ := hK_compact.isBounded.subset_closedBall 0
    refine ⟨R, fun x hx => hR ?_⟩
    by_contra hxK
    have hVx : c < V x := hK (Set.mem_compl hxK)
    exact absurd hVx (not_lt.mpr hx)
